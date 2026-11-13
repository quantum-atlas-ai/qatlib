/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SignalPrimitive.GridGradient.GradientSourceContinuationDefs

/-!
# Value kickback and Fourier gradient continuation

This module proves the compute, phase kickback, and uncompute action of a modular value oracle,
including restoration of the value register and explicit resource counts. It then transports
phase residual bounds to Fourier gradient windows, in the numerical estimation setting of
[Jordan2005Gradient].

Centered decoding estimates, dyadic output certificates, examples without exact low precision
records, and register ledgers are collected into three continuation endpoint theorems.

## Main statements

* `value_compute_kickback_uncompute_actual`: the exact phase action with a clean value register.
* `value_compute_kickback_uncompute_operator_error`: operator error from phase error modulo
  integers.
* `centered_output_estimate_error`: coordinate accuracy on a good modular window.
* `gext1_endpoint`, `gext2_endpoint`, and `gext3_endpoint`: the three continuation
  specifications.

## References

* [Jordan, 2005][Jordan2005Gradient]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SignalPrimitive.GridGradient
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.HspRecovery.Reduction.GradientOracle
open Qatlib.Concepts.GradientOracle.ValueKickback
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.SignalPrimitive.GridGradient

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Qatlib.Concepts.FourierRecovery.ModularFourier.GradientSourceContinuation

open Qatlib
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexConjugate

/-- The gradient value oracle is the additive oracle for the same modular value function. -/
private theorem gradientValueOracle_eq_addOracle {X : Type} [Fintype X] [DecidableEq X]
    (Q : ℕ) [NeZero Q] (v : X → ZMod Q) : gradientValueOracle Q v = AddOracle v := by
  rw [addOracle_eq_permMatrix]
  ext x y
  simp [gradientValueOracle, permMatrix, addOracleEquiv, Prod.ext_iff]

/-- Applying a matrix gate commutes with scalar multiplication of the input state. -/
private theorem applyGate_smul {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (c : ℂ) (ψ : QState I) : ApplyGate A (c • ψ) = c • ApplyGate A ψ := by
  funext i
  show (∑ j, A i j * (c * ψ j)) = c * (∑ j, A i j * ψ j)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Applying a matrix to a basis ket returns its corresponding column. -/
private theorem applyGate_matrix_ket {J : Type*} [Fintype J] [DecidableEq J]
    (P : Matrix J J ℂ) (y : J) : ApplyGate P (Qatlib.Foundations.PureStateMath.Ket y) = fun i => P i y := by
  funext i
  show (∑ j, P i j * Qatlib.Foundations.PureStateMath.Ket y j) = P i y
  simp [Qatlib.Foundations.PureStateMath.Ket]

/-- The tensor product of the identity and a diagonal gate multiplies a basis ket by the
corresponding diagonal coefficient. -/
private theorem tensorGate_one_diag_ket {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (d : J → ℂ) (x : I) (y : J) :
    ApplyGate (TensorGate (1 : Matrix I I ℂ) (Matrix.diagonal d))
      (Qatlib.Foundations.PureStateMath.Ket (x, y)) = d y • Qatlib.Foundations.PureStateMath.Ket (x, y) := by
  rw [← tensorState_ket_ket, applyGate_tensorGate, applyGate_one, applyGate_matrix_ket]
  funext p
  cases p with
  | mk i j =>
    simp only [TensorState, Pi.smul_apply, smul_eq_mul]
    by_cases hx : i = x <;> by_cases hy : j = y <;>
      simp [hx, hy, Qatlib.Foundations.PureStateMath.Ket, Matrix.diag_apply, Prod.ext_iff]

/-- The modular value phase gate is unitary. -/
private theorem valuePhaseGate_unitary (Q : ℕ) [NeZero Q] :
    valuePhaseGate Q ∈ Matrix.unitaryGroup (ZMod Q) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  simp only [valuePhaseGate, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext y
  have hconj : conj (valuePhaseCoeff Q y)
      = Complex.exp (-(((2 * Real.pi * ((y.val : ℝ) / (Q : ℝ)) : ℝ) : ℂ) * Complex.I)) := by
    rw [valuePhaseCoeff, ← Complex.exp_conj]
    congr 1
    rw [map_mul conj, Complex.conj_ofReal, Complex.conj_I]
    ring
  show conj (valuePhaseCoeff Q y) * valuePhaseCoeff Q y = 1
  rw [hconj, valuePhaseCoeff, ← Complex.exp_add]
  have hz : -(((2 * Real.pi * ((y.val : ℝ) / (Q : ℝ)) : ℝ) : ℂ) * Complex.I)
      + (((2 * Real.pi * ((y.val : ℝ) / (Q : ℝ)) : ℝ) : ℂ) * Complex.I) = 0 := by ring
  rw [hz, Complex.exp_zero]

/-- Adding an integer to a real phase leaves its `2 * π * i` complex exponential unchanged. -/
private theorem exp_two_pi_I_shift_int (t : ℝ) (n : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * (Complex.ofReal (t + (n : ℝ))))
      = Complex.exp (2 * Real.pi * Complex.I * (Complex.ofReal t)) := by
  have h : 2 * Real.pi * Complex.I * (Complex.ofReal (t + (n : ℝ)))
      = 2 * Real.pi * Complex.I * (Complex.ofReal t)
        + 2 * Real.pi * Complex.I * (Complex.ofReal ((n : ℤ) : ℝ)) := by
    push_cast
    ring
  rw [h, Complex.exp_add, exp_two_pi_I_int, mul_one]

/-- The compute, phase kickback, and uncompute word multiplies a basis state with zero value
register by the value phase and restores the value register to zero. -/
theorem value_compute_kickback_uncompute_actual :
    ∀ (d M Q : ℕ) [NeZero Q] (v : GradientGrid d M → ZMod Q) (x : GradientGrid d M),
      (evaluate (gradientValueOracle Q v) (valueComputeKickbackUncomputeWord d M Q)) *ᵥ
          (Qatlib.Foundations.PureStateMath.Ket (x, (0 : ZMod Q))) =
        valuePhaseCoeff Q (v x) • Qatlib.Foundations.PureStateMath.Ket (x, (0 : ZMod Q)) := by
  intro d M Q _ v x
  have hcomp : evaluate (gradientValueOracle Q v) (valueComputeKickbackUncomputeWord d M Q)
      = (gradientValueOracle Q v)ᴴ *
        (TensorGate (1 : Matrix (GradientGrid d M) (GradientGrid d M) ℂ) (valuePhaseGate Q) *
          (gradientValueOracle Q v)) := by
    simp [evaluate, instructionMatrix, valueComputeKickbackUncomputeWord, Matrix.mul_one]
  have hO : gradientValueOracle Q v = AddOracle v := gradientValueOracle_eq_addOracle Q v
  have hOh : (gradientValueOracle Q v)ᴴ = AddOracle (-v) := by
    rw [hO, addOracle_conjTranspose]
  have hket : ApplyGate (AddOracle v) (Qatlib.Foundations.PureStateMath.Ket (x, (0 : ZMod Q))) = Ket (x, v x) := by
    rw [applyGate_addOracle_ket]
    simp
  have hket2 : ApplyGate (AddOracle (-v)) (Ket (x, v x)) = Ket (x, (0 : ZMod Q)) := by
    rw [applyGate_addOracle_ket]
    simp
  rw [hcomp, hOh, hO]
  show ApplyGate (AddOracle (-v) *
        (TensorGate (1 : Matrix (GradientGrid d M) (GradientGrid d M) ℂ) (valuePhaseGate Q) *
          AddOracle v))
      (Qatlib.Foundations.PureStateMath.Ket (x, (0 : ZMod Q))) = _
  rw [applyGate_mul, applyGate_mul]
  rw [hket]
  rw [valuePhaseGate]
  rw [tensorGate_one_diag_ket]
  rw [applyGate_smul]
  rw [hket2]

/-- The value kickback word is well formed, has two queries and one gate, and uses the stated
modular value register bit budget. -/
theorem value_compute_kickback_uncompute_resources :
    ∀ (d M Q : ℕ) [NeZero Q],
      WellFormedAdjointCircuit (valueComputeKickbackUncomputeWord d M Q) ∧
      adjointQueryCount (valueComputeKickbackUncomputeWord d M Q) = 2 ∧
      adjointGateCount (valueComputeKickbackUncomputeWord d M Q) = 1 ∧
      valueRegisterBits Q = Nat.clog 2 (max 2 Q) := by
  intro d M Q _
  refine ⟨?_, rfl, rfl, rfl⟩
  rw [valueComputeKickbackUncomputeWord, WellFormedAdjointCircuit.backward_cons_iff,
    WellFormedAdjointCircuit.gate_cons_iff, WellFormedAdjointCircuit.forward_cons_iff]
  exact ⟨tensorGate_unitary (one_mem (Matrix.unitaryGroup _ ℂ))
      (valuePhaseGate_unitary Q), WellFormedAdjointCircuit.nil⟩

/-- Adding an integer valued function to a gradient phase leaves its phase operator unchanged. -/
theorem gradientPhase_int_shift (d M : ℕ) (φ : GradientGrid d M → ℝ)
    (k : GradientGrid d M → ℤ) :
    gradientPhase d M (fun x => φ x + (k x : ℝ)) = gradientPhase d M φ := by
  unfold gradientPhase
  congr 1
  funext x
  exact exp_two_pi_I_shift_int (φ x) (k x)

/-- A value phase error at most `δ` modulo integers bounds the norm of the phase operator
difference by `2 * π * δ`. -/
theorem value_compute_kickback_uncompute_operator_error :
    ∀ (d M Q : ℕ) [NeZero Q] (v : GradientGrid d M → ZMod Q)
      (φ : GradientGrid d M → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
      (herror : ∀ x, ∃ k : ℤ, |gradientValuePhase Q v x - φ x - k| ≤ δ),
      ‖gradientPhase d M (gradientValuePhase Q v) - gradientPhase d M φ‖ ≤ 2 * Real.pi * δ := by
  intro d M Q _ v φ δ hδ herror
  let κ : GradientGrid d M → ℤ := fun x => Classical.choose (herror x)
  have hspec (x : GradientGrid d M) : |gradientValuePhase Q v x - φ x - κ x| ≤ δ := by
    exact Classical.choose_spec (herror x)
  have hshift : gradientPhase d M
        (fun x => gradientValuePhase Q v x + ↑(-κ x))
      = gradientPhase d M (gradientValuePhase Q v) :=
    gradientPhase_int_shift d M (gradientValuePhase Q v) (fun x => -κ x)
  have hpoint (x : GradientGrid d M) :
      |gradientValuePhase Q v x + ↑(-κ x) - φ x| ≤ δ := by
    have h := abs_le.mp (hspec x)
    have heq : |gradientValuePhase Q v x + ↑(-κ x) - φ x|
        = |gradientValuePhase Q v x - φ x - (κ x : ℝ)| := by
      congr 1
      simp only [Int.cast_neg]
      ring
    rw [heq]
    exact abs_le.mpr h
  have h := gradientPhase_sub_norm_le d M
    (fun x => gradientValuePhase Q v x + ↑(-κ x)) φ δ hδ hpoint
  rw [hshift] at h
  exact h

/-- A stationary phase residual bounded within `B` of a constant gives window probability at
least `1 - 16 * d / (M * w) - 4 * π * B` under the stated positivity conditions. -/
theorem stationary_phase_window_transport :
    ∀ (d M : ℕ) (hM : 0 < M) (g : Fin d → ℝ) (c w B : ℝ) (φ : GradientGrid d M → ℝ)
      (hM2 : 2 ≤ M) (hw : 0 < w) (hB : 0 ≤ B)
      (herror : ∀ x, |stationaryPhaseResidual d M φ g x - (c : ℝ)| ≤ B),
      MeasureProb (gradientReadout d M hM φ)
        (Finset.univ.filter (fun z => ∀ j : Fin d,
          phaseDistance ((z j).val / (M : ℝ)) (g j) ≤ w))
        ≥ 1 - 16 * (d : ℝ) / ((M : ℝ) * w) - 4 * Real.pi * B := by
  intro d M hM g c w B φ hM2 hw hB herror
  have hpoint (x : GradientGrid d M) :
      |φ x - (c + ∑ j : Fin d, g j * (x j).val)| ≤ B := by
    have h := abs_le.mp (herror x)
    have hres : stationaryPhaseResidual d M φ g x = φ x - ∑ j : Fin d, g j * (x j).val := rfl
    have heq : |φ x - (c + ∑ j : Fin d, g j * (x j).val)|
        = |stationaryPhaseResidual d M φ g x - c| := by
      congr 1
      rw [hres]
      ring
    rw [heq]
    exact abs_le.mpr h
  exact gradient_actual_phase_error_transport d M hM g c w B φ hM2 hw hB hpoint

/-- A good modular window sample gives centered coordinate errors at most `w` when the gradient
and window satisfy the stated bounds. -/
theorem centered_output_estimate_error :
    ∀ (d M : ℕ) (hM : 0 < M) (g : Fin d → ℝ) (w : ℝ)
      (hg : ∀ j : Fin d, |g j| ≤ 1 / 4) (hw : w ≤ 1 / 8)
      (z : GradientGrid d M)
      (hgood : ∀ j : Fin d, phaseDistance ((z j).val / (M : ℝ)) (g j) ≤ w),
      ∀ j : Fin d, |gradientEstimate d M z j - g j| ≤ w := by
  intro d M hM g w hg hw z hgood j
  have h := gradient_signed_decode_window M hM (z j) (g j) w (hg j) hw (hgood j)
  simpa only [gradientEstimate, centeredGridOutput] using! h

/-- Every label on a grid of size `2^m` satisfies `DyadicGridLabel m`. -/
theorem dyadic_grid_label (m : ℕ) (z : Fin (2 ^ m)) : DyadicGridLabel m z := by
  refine ⟨z.val, ?_⟩
  push_cast
  ring

/-- Every centered output on a grid of size `2^m` is an integer multiple of `2^(-m)`. -/
theorem centered_output_dyadic (m : ℕ) (z : Fin (2 ^ m)) :
    ∃ n : ℤ, centeredGridOutput (2 ^ m) z = (n : ℝ) / (2 : ℝ) ^ m := by
  unfold centeredGridOutput signedGridValue
  split_ifs with h
  · refine ⟨z.val, ?_⟩
    push_cast
    ring
  · refine ⟨z.val - (2 ^ m : ℤ), ?_⟩
    push_cast
    field_simp

/-- The uncentered real coordinate of a grid label of size `2^m` has an exact precision `m`
record. -/
theorem dyadic_grid_record (m : ℕ) (z : Fin (2 ^ m)) :
    GeneralRealRecord m ((z.val : ℝ) / (2 : ℝ) ^ m) := by
  refine ⟨z.val, ?_⟩
  push_cast
  ring

/-- For natural `Q > 1`, the reciprocal `1 / Q` has no exact real record at precision zero. -/
theorem non_dyadic_reciprocal (Q : ℕ) (hQ : 1 < Q) :
    ¬ GeneralRealRecord 0 ((1 : ℝ) / Q) := by
  rintro ⟨n, hn⟩
  have h2 : (1 : ℝ) / Q = ((n : ℤ) : ℝ) := by
    simpa [div_one, one_pow] using! hn
  have h3 : ((n : ℤ) : ℝ) * (Q : ℝ) = 1 := by
    rw [← h2]
    field_simp
  have hQpos : (0 : ℝ) < (Q : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hQ)
  have hQ2 : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  rcases Int.lt_trichotomy 0 n with hpos | hzero | hneg
  · have hn1 : (1 : ℤ) ≤ n := by omega
    have hn1R : (1 : ℝ) ≤ ((n : ℤ) : ℝ) := by exact_mod_cast hn1
    have hmul : (1 : ℝ) * (Q : ℝ) ≤ ((n : ℤ) : ℝ) * (Q : ℝ) :=
      mul_le_mul_of_nonneg_right hn1R (le_of_lt hQpos)
    linarith
  · rw [← hzero] at h3
    norm_num at h3
  · have hnle : ((n : ℤ) : ℝ) ≤ 0 := by
      have hle : n ≤ 0 := by omega
      simpa using! (Int.cast_le).mpr hle
    have hmul : ((n : ℤ) : ℝ) * (Q : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hnle (le_of_lt hQpos)
    linarith

/-- The value `1 / 3` has no exact real record at precision zero or one. -/
theorem non_dyadic_one_third : ¬ GeneralRealRecord 0 (1 / 3) ∧
    ¬ GeneralRealRecord 1 (1 / 3) := by
  constructor
  · rintro ⟨n, hn⟩
    have hn' : (1 : ℝ) = 3 * ((n : ℤ) : ℝ) := by
      have h2 := hn
      field_simp at h2
      linarith
    have hnint : (3 : ℤ) * n = 1 := by exact_mod_cast hn'.symm
    omega
  · rintro ⟨n, hn⟩
    have hn' : (2 : ℝ) = 3 * ((n : ℤ) : ℝ) := by
      have h2 := hn
      field_simp at h2
      linarith
    have hnint : (3 : ℤ) * n = 2 := by exact_mod_cast hn'.symm
    omega

/-- The gradient readout word is unitary and has one query and `2 * d` gates for positive grid
size. -/
theorem clause3_readout_word_ledger (d M : ℕ) (hM : 0 < M) :
    IsUnitaryCircuit (gradientWord d M) ∧
      QueryCount (gradientWord d M) = 1 ∧
      GateCount (gradientWord d M) = 2 * d :=
  gradient_coordinate_qft_word_unitarity d M hM

/-- The readout integer budget is `K + k`, and its space budget is `d * Nat.clog 2 (max 2 M) + K
+ k`. -/
theorem clause3_readout_bit_and_space_ledger (d M K k : ℕ) :
    readoutIntegerBits K k = K + k ∧
      readoutSpaceBits d M K k = d * Nat.clog 2 (max 2 M) + K + k :=
  ⟨rfl, rfl⟩

/-- The one coordinate gradient estimate on a grid of size `2^m` is an integer multiple of
`2^(-m)`. -/
theorem clause3_estimate_is_dyadic (m : ℕ) (z : Fin (2 ^ m)) :
    ∃ n : ℤ, gradientEstimate 1 (2 ^ m) (fun _ => z) 0 = (n : ℝ) / (2 : ℝ) ^ m := by
  obtain ⟨n, hn⟩ := centered_output_dyadic m z
  refine ⟨n, ?_⟩
  simpa only [gradientEstimate, centeredGridOutput] using! hn

/-- A coordinatewise estimate error bound `w` gives the magnitude bound `|ê j| ≤ |g j| + w`. -/
theorem clause3_estimate_magnitude_bound (d : ℕ) (g ê : Fin d → ℝ) (w : ℝ)
    (herror : ∀ j : Fin d, |ê j - g j| ≤ w) :
    ∀ j : Fin d, |ê j| ≤ |g j| + w := by
  intro j
  have h := abs_le.mp (herror j)
  calc
    |ê j| = |g j + (ê j - g j)| := by
      congr 1
      ring
    _ ≤ |g j| + |ê j - g j| := abs_add_le _ _
    _ ≤ |g j| + w := by
      have habs : |ê j - g j| ≤ w := abs_le.mpr h
      linarith

/-- Establishes the first gradient continuation specification, combining value kickback, phase
invariance and perturbation bounds, stationary phase transport, and exact affine readout. -/
theorem gext1_endpoint : stageB_fourier_gradient_gext1_spec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d M Q _ v x
    exact value_compute_kickback_uncompute_actual d M Q v x
  · intro d M Q _
    obtain ⟨hW, hq, hg, _⟩ := value_compute_kickback_uncompute_resources d M Q
    exact ⟨hW, hq, hg⟩
  · intro d M φ k
    exact gradientPhase_int_shift d M φ k
  · intro d M Q _ v φ δ hδ herror
    exact value_compute_kickback_uncompute_operator_error d M Q v φ δ hδ herror
  · intro d M hM g c w B φ hM2 hw hB herror
    exact stationary_phase_window_transport d M hM g c w B φ hM2 hw hB herror
  · intro d M hM q c
    exact gradient_affine_actual_exact_readout d M hM q c

/-- Establishes the second gradient continuation specification, combining centered decoding,
window probability, dyadic records, and the stated obstructions to exact records. -/
theorem gext2_endpoint : stageB_fourier_gradient_gext2_spec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d M hM g w hg hw z hgood
    exact centered_output_estimate_error d M hM g w hg hw z hgood
  · intro d M hM g c w B φ hM2 hw hB herror
    exact stationary_phase_window_transport d M hM g c w B φ hM2 hw hB herror
  · intro m z
    exact dyadic_grid_label m z
  · intro m z
    exact centered_output_dyadic m z
  · intro m z
    exact dyadic_grid_record m z
  · exact (non_dyadic_one_third.1)
  · exact (non_dyadic_one_third.2)
  · intro Q hQ
    exact non_dyadic_reciprocal Q hQ

/-- Establishes the third gradient continuation specification, combining readout and value
register resource ledgers, dyadic estimates, and estimate magnitude bounds. -/
theorem gext3_endpoint : stageB_fourier_gradient_gext3_spec := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro d M hM
    exact clause3_readout_word_ledger d M hM
  · intro d M _ K k
    exact clause3_readout_bit_and_space_ledger d M K k
  · intro d M Q _
    rfl
  · intro m z
    exact clause3_estimate_is_dyadic m z
  · intro d M hM g w hg hw ê herror
    exact clause3_estimate_magnitude_bound d g ê w herror

end Qatlib.Concepts.FourierRecovery.ModularFourier.GradientSourceContinuation
