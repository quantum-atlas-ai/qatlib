/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.NearGridHHLOutput
import Mathlib.Basic.Real.Sign

/-!
# Clipped reciprocal filters for uniform HHL

This module defines a signed clipped reciprocal amplitude, its Boolean flag rotation, and the
counted uniform HHL word. It proves phase-kernel tail bounds and local filter continuity used in
the off-grid analysis of the HHL method [HarrowHassidimLloyd2009].

The good-label and tail estimates combine into a kernel-weighted squared rotation-error bound
with an explicit grid requirement.

## Main statements

* `uniformHHLRotation_unitary`: unitarity of the clipped rotation for positive `d`.
* `uniform_hhl_actual_legal_forward_inverse_ledger`: legality and exact instruction counts.
* `uniform_hhl_clipped_rotation_and_local_continuity`: local rotation stability away from zero.
* `uniformHHL_spectral_window_error`: mean squared flag-rotation error at most `η^2`.

## References

* [Harrow et al., 2009][HarrowHassidimLloyd2009]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.NativeNumerics.LayeredMean
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.HhlAlgorithms.GridExactHHL

open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false

namespace Qatlib.Concepts.HhlAlgorithms.UniformHHL

open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- Circular phase distance is at most `1/2`. -/
theorem uniform_phaseDistance_le_half (x y : ℝ) : phaseDistance x y ≤ 1 / 2 := by
  unfold phaseDistance
  apply abs_le.mpr
  have h₀ := Int.floor_le (x - y + 1 / 2)
  have h₁ := Int.lt_floor_add_one (x - y + 1 / 2)
  constructor <;> linarith

/-- The complex chord length at phase `t` is at least four times its circular distance from
zero. -/
theorem uniform_phase_chord_lower (t : ℝ) :
    4 * phaseDistance t 0 ≤ ‖Complex.exp (2 * Real.pi * Complex.I * t) - 1‖ := by
  let n : ℤ := ⌊t + 1 / 2⌋
  let r : ℝ := t - (n : ℝ)
  have hr : |r| ≤ 1 / 2 := by
    simpa [phaseDistance, r, n] using! uniform_phaseDistance_le_half t 0
  have he : Complex.exp (2 * Real.pi * Complex.I * t) =
      Complex.exp (2 * Real.pi * Complex.I * r) := by
    have ht : (2 * Real.pi * Complex.I * t : ℂ) =
        2 * Real.pi * Complex.I * r + 2 * Real.pi * Complex.I * (n : ℝ) := by
      dsimp [r]
      push_cast
      ring
    rw [ht, Complex.exp_add, exp_two_pi_I_int, mul_one]
  have hi : (2 * Real.pi * Complex.I * r : ℂ) =
      Complex.I * ((2 * Real.pi * r : ℝ) : ℂ) := by push_cast; ring
  rw [he, hi, Complex.norm_exp_I_mul_ofReal_sub_one,
    show (2 * Real.pi * r) / 2 = Real.pi * r by ring,
    Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hs := Real.mul_abs_le_abs_sin (x := Real.pi * r) (by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos])
  rw [abs_mul, abs_of_pos Real.pi_pos] at hs
  have hc : 2 / Real.pi * (Real.pi * |r|) = 2 * |r| := by
    field_simp
  rw [hc] at hs
  simp only [phaseDistance, sub_zero]
  change 4 * |r| ≤ _
  linarith

/-- A phase-kernel amplitude at circular distance greater than `w > 0` is at most `1/(2*M*w)`. -/
theorem uniform_qpeKernel_bad_label (M : ℕ) (φ w : ℝ) (y : Fin M)
    (hM : 0 < M) (hw : 0 < w)
    (hy : w < phaseDistance φ ((y.val : ℝ) / (M : ℝ))) :
    ‖qpeKernel M φ y‖ ≤ 1 / (2 * (M : ℝ) * w) := by
  have hm : 0 < (M : ℝ) := by exact_mod_cast hM
  have hg := congrArg norm (qpeKernel_geometric_identity M φ y hM)
  push_cast at hg
  rw [norm_mul, norm_mul, Complex.norm_natCast] at hg
  have hn : ‖Complex.exp (2 * Real.pi * Complex.I * ((M : ℝ) * φ)) - 1‖ ≤ 2 := by
    push_cast
    calc
      _ ≤ ‖Complex.exp (2 * Real.pi * Complex.I * ((M : ℂ) * (φ : ℂ)))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by
        have he := norm_exp_two_pi_I ((M : ℝ) * φ)
        push_cast at he
        rw [he]
        norm_num
  push_cast at hn
  have hl := uniform_phase_chord_lower (φ - (y.val : ℝ) / (M : ℝ))
  have hd : phaseDistance (φ - (y.val : ℝ) / (M : ℝ)) 0 =
      phaseDistance φ ((y.val : ℝ) / (M : ℝ)) := by simp [phaseDistance]
  rw [hd] at hl
  push_cast at hl
  have hp := mul_le_mul_of_nonneg_left hl
    (mul_nonneg hm.le (norm_nonneg (qpeKernel M φ y)))
  apply (le_div_iff₀ (by positivity : 0 < 2 * (M : ℝ) * w)).mpr
  have hb := mul_le_mul_of_nonneg_left hy.le
    (mul_nonneg hm.le (norm_nonneg (qpeKernel M φ y)))
  nlinarith

/-- For `M ≥ 2` and `0 < w ≤ 1/2`, the total squared kernel mass beyond circular distance `w` is
at most `1/(4*M*w^2)`. -/
theorem uniform_phase_kernel_derived_tail :
    ∀ (M : ℕ) (φ w : ℝ), 2 ≤ M → 0 < w → w ≤ 1 / 2 →
      (∑ y ∈ Finset.univ.filter (fun y : Fin M =>
        w < phaseDistance φ ((y.val : ℝ) / (M : ℝ))), ‖qpeKernel M φ y‖ ^ 2)
        ≤ 1 / (4 * (M : ℝ) * w ^ 2) := by
  intro M φ w hM hw _
  have hm : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  let s := Finset.univ.filter (fun y : Fin M =>
    w < phaseDistance φ ((y.val : ℝ) / (M : ℝ)))
  have hs : (s.card : ℝ) ≤ M := by
    exact_mod_cast (show s.card ≤ M from
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp))
  calc
    _ ≤ ∑ _y ∈ s, (1 / (2 * (M : ℝ) * w)) ^ 2 := by
      apply Finset.sum_le_sum
      intro y hy
      have hy' := (Finset.mem_filter.mp hy).2
      exact pow_le_pow_left₀ (norm_nonneg _)
          (uniform_qpeKernel_bad_label M φ w y (by omega) hw hy') 2
    _ = (s.card : ℝ) * (1 / (2 * (M : ℝ) * w)) ^ 2 := by simp
    _ ≤ (M : ℝ) * (1 / (2 * (M : ℝ) * w)) ^ 2 :=
      mul_le_mul_of_nonneg_right hs (sq_nonneg _)
    _ = _ := by field_simp; ring

/-- The signed clipped reciprocal amplitude `(d/4) * sign x / max (d/2) |x|`. -/
noncomputable def uniformHHLGamma (d x : ℝ) : ℝ :=
  (d / 4) * Real.sign x / max (d / 2) |x|

/-- For positive `d`, the clipped reciprocal amplitude has absolute value at most `1/2`. -/
theorem uniformHHLGamma_abs_le (d x : ℝ) (hd : 0 < d) :
    |uniformHHLGamma d x| ≤ 1 / 2 := by
  have hden : 0 < max (d / 2) |x| := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hs : |Real.sign x| ≤ 1 := by
    rcases Real.sign_apply_eq x with h | h | h <;> rw [h] <;> norm_num
  rw [uniformHHLGamma, abs_div, abs_mul,
    abs_of_pos (by linarith : 0 < d / 4), abs_of_pos hden]
  apply (div_le_iff₀ hden).mpr
  have hm := le_max_left (d / 2) |x|
  nlinarith

/-- The real Boolean rotation with sine amplitude `γ = uniformHHLGamma d x` and nonnegative
cosine amplitude `sqrt (1-γ^2)`. -/
noncomputable def uniformHHLRotation (d x : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.of fun p q => match p, q with
    | false, false => (Real.sqrt (1 - uniformHHLGamma d x ^ 2) : ℂ)
    | true, false => (uniformHHLGamma d x : ℂ)
    | false, true => (-(uniformHHLGamma d x) : ℂ)
    | true, true => (Real.sqrt (1 - uniformHHLGamma d x ^ 2) : ℂ)

/-- The clipped reciprocal flag rotation is unitary for positive `d`. -/
theorem uniformHHLRotation_unitary (d x : ℝ) (hd : 0 < d) :
    uniformHHLRotation d x ∈ Matrix.unitaryGroup Bool ℂ := by
  have ha := uniformHHLGamma_abs_le d x hd
  have hrad : 0 ≤ 1 - uniformHHLGamma d x ^ 2 := by
    nlinarith [sq_abs (uniformHHLGamma d x), abs_nonneg (uniformHHLGamma d x)]
  have hone : (Real.sqrt (1 - uniformHHLGamma d x ^ 2) : ℂ) *
      (Real.sqrt (1 - uniformHHLGamma d x ^ 2) : ℂ) +
      (uniformHHLGamma d x : ℂ) * (uniformHHLGamma d x : ℂ) = 1 := by
    have hr : Real.sqrt (1 - uniformHHLGamma d x ^ 2) *
        Real.sqrt (1 - uniformHHLGamma d x ^ 2) +
        uniformHHLGamma d x * uniformHHLGamma d x = 1 := by
      nlinarith [Real.sq_sqrt hrad]
    exact_mod_cast hr
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext p q
  simp only [Matrix.mul_apply, Matrix.one_apply]
  show ∑ r : Bool, (starRingEnd ℂ) (uniformHHLRotation d x r p) *
    uniformHHLRotation d x r q = (if p = q then 1 else 0)
  cases p <;> cases q
  · simp only [uniformHHLRotation, Matrix.of_apply, Fintype.sum_bool,
      Complex.conj_ofReal, ite_true]
    simpa only [add_comm] using! hone
  · simp [uniformHHLRotation]; ring
  · simp [uniformHHLRotation]; ring
  · simp [uniformHHLRotation, hone]

/-- Decode a phase label as `y/M` up to the midpoint and as `y/M - 1` above it. -/
noncomputable def uniformHHLDecode (M : ℕ) (y : Fin M) : ℝ :=
  if 2 * y.val ≤ M then (y.val : ℝ) / (M : ℝ)
  else (y.val : ℝ) / (M : ℝ) - 1

/-- The phase-label-controlled clipped rotation on the Boolean flag, leaving the data register
unchanged. -/
noncomputable def uniformHHLFlag {D M : ℕ} (d : ℝ) :
    Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ :=
  relabelGate (gridHHLFlagData (D := D) (M := M))
    (TensorGate (BlockDiag (fun y : Fin M => uniformHHLRotation d (uniformHHLDecode M y)))
      (1 : Operator D))

/-- The decoded-label flag gate is unitary for positive `d`. -/
theorem uniformHHLFlag_unitary {D M : ℕ} (d : ℝ) (hd : 0 < d) :
    uniformHHLFlag (D := D) (M := M) d ∈ Matrix.unitaryGroup _ ℂ := by
  apply (relabelGate_mem_unitaryGroup _ _).2
  exact tensorGate_unitary (blockDiag_unitary _ fun y => uniformHHLRotation_unitary d _ hd)
    (Submonoid.one_mem _)

/-- The counted uniform HHL word formed from preparation, forward phase estimation, the clipped
flag rotation, and adjoint uncomputation. -/
noncomputable def uniformHHLWord {D : ℕ} (M : ℕ) (d : ℝ) (B : Operator D) :
    List (AdjointStep (Fin M × (Bool × (Bool × Fin D)))) :=
  adjointCircuit (countedQPEWord D M) ++ [.gate (countedHHLLiftGate (uniformHHLFlag d))] ++
    countedQPEWord D M ++ [.gate (countedHHLLiftGate (countedHHLPrepMain B))]

/-- For `M ≥ 2`, positive `d`, and unitary input preparation, the uniform HHL word is well
formed with `2*(M-1)` queries and `4*(M-1)+6` gates. -/
theorem uniform_hhl_actual_legal_forward_inverse_ledger :
    ∀ (D M : ℕ) (d : ℝ) (B : Operator D), 2 ≤ M → 0 < d →
      B ∈ Matrix.unitaryGroup (Fin D) ℂ →
      WellFormedAdjointCircuit (uniformHHLWord M d B) ∧
        adjointQueryCount (uniformHHLWord M d B) = 2 * (M - 1) ∧
        adjointGateCount (uniformHHLWord M d B) = 4 * (M - 1) + 6 := by
  intro D M d B hM hd hB
  have hm : 0 < M := by omega
  have hwf := countedQPEWord_wellFormed D M hm
  refine ⟨?_, ?_, ?_⟩
  · simp only [uniformHHLWord, WellFormedAdjointCircuit.append_iff,
      WellFormedAdjointCircuit.gate_cons_iff, WellFormedAdjointCircuit.nil, and_true]
    exact ⟨⟨⟨hwf.adjointCircuit, countedHHLLiftGate_unitary (uniformHHLFlag_unitary d hd)⟩,
      hwf⟩, countedHHLLiftGate_unitary (countedHHLPrepMain_unitary hB)⟩
  · rw [uniformHHLWord, adjointQueryCount_append, adjointQueryCount_append,
      adjointQueryCount_append, adjointQueryCount_adjointCircuit,
      (countedQPEWord_counts D M hm).1]
    simp only [adjointQueryCount]
    omega
  · rw [uniformHHLWord, adjointGateCount_append, adjointGateCount_append,
      adjointGateCount_append, adjointGateCount_adjointCircuit,
      (countedQPEWord_counts D M hm).2]
    simp only [adjointGateCount]
    omega

/-- Outside the clipped region `|x| ≥ d/2`, the amplitude equals `d/(4*x)` when `d > 0`. -/
theorem uniformHHLGamma_eq_reciprocal (d x : ℝ) (hd : 0 < d)
    (hx : d / 2 ≤ |x|) : uniformHHLGamma d x = d / (4 * x) := by
  have hxn : x ≠ 0 := by intro h; subst x; simp at hx; linarith
  rw [uniformHHLGamma, max_eq_right hx]
  rcases hxn.lt_or_gt with hn | hp
  · rw [Real.sign_of_neg hn, abs_of_neg hn]
    field_simp
  · rw [Real.sign_of_pos hp, abs_of_pos hp]
    field_simp

/-- For `|a|, |b| ≤ 1/2`, the difference of the nonnegative cosine amplitudes is at most
`|a-b|`. -/
theorem uniformHHL_cosine_difference (a b : ℝ) (ha : |a| ≤ 1 / 2)
    (hb : |b| ≤ 1 / 2) :
    |Real.sqrt (1 - a ^ 2) - Real.sqrt (1 - b ^ 2)| ≤ |a - b| := by
  have ha2 : a ^ 2 ≤ 1 / 4 := by nlinarith [sq_abs a, abs_nonneg a]
  have hb2 : b ^ 2 ≤ 1 / 4 := by nlinarith [sq_abs b, abs_nonneg b]
  have hsa := Real.sq_sqrt (show 0 ≤ 1 - a ^ 2 by linarith)
  have hsb := Real.sq_sqrt (show 0 ≤ 1 - b ^ 2 by linarith)
  have hsa0 := Real.sqrt_nonneg (1 - a ^ 2)
  have hsb0 := Real.sqrt_nonneg (1 - b ^ 2)
  have hsa1 : 1 / 2 ≤ Real.sqrt (1 - a ^ 2) := by nlinarith
  have hsb1 : 1 / 2 ≤ Real.sqrt (1 - b ^ 2) := by nlinarith
  have he : (Real.sqrt (1 - a ^ 2) - Real.sqrt (1 - b ^ 2)) *
      (Real.sqrt (1 - a ^ 2) + Real.sqrt (1 - b ^ 2)) = (b - a) * (b + a) := by
    nlinarith
  have heabs := congrArg abs he
  rw [abs_mul, abs_mul, abs_of_nonneg (add_nonneg hsa0 hsb0), abs_sub_comm b a] at heabs
  have hab : |b + a| ≤ 1 := (abs_add_le b a).trans (by linarith)
  have hprod := mul_le_mul_of_nonneg_left hab (abs_nonneg (a - b))
  have hden := mul_le_mul_of_nonneg_left
    (show 1 ≤ Real.sqrt (1 - a ^ 2) + Real.sqrt (1 - b ^ 2) by linarith)
    (abs_nonneg (Real.sqrt (1 - a ^ 2) - Real.sqrt (1 - b ^ 2)))
  nlinarith

/-- The distance between rotated zero-flag states is at most twice the difference of their
clipped reciprocal amplitudes. -/
theorem uniformHHLRotation_vector_difference (d x y : ℝ) (hd : 0 < d) :
    ‖toEuclidean_fromVec (uniformHHLRotation d x *ᵥ Ket false -
      uniformHHLRotation d y *ᵥ Ket false)‖ ≤ 2 * |uniformHHLGamma d x - uniformHHLGamma d y| := by
  have hcos := uniformHHL_cosine_difference _ _
    (uniformHHLGamma_abs_le d x hd) (uniformHHLGamma_abs_le d y hd)
  have hs := norm_toEuclidean_fromVec_sq (uniformHHLRotation d x *ᵥ Ket false -
    uniformHHLRotation d y *ᵥ Ket false)
  have hk (A : Matrix Bool Bool ℂ) (b : Bool) : (A *ᵥ Ket false) b = A b false := by
    simp [Matrix.mulVec, dotProduct, Ket]
  simp only [Fintype.sum_bool, Pi.sub_apply, hk,
    uniformHHLRotation, Matrix.of_apply] at hs
  rw [← Complex.ofReal_sub, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs] at hs
  change ‖toEuclidean_fromVec (uniformHHLRotation d x *ᵥ Ket false -
    uniformHHLRotation d y *ᵥ Ket false)‖ ^ 2 = _ at hs
  have hc := pow_le_pow_left₀ (abs_nonneg _) hcos 2
  have hn := norm_nonneg (toEuclidean_fromVec
    (uniformHHLRotation d x *ᵥ Ket false - uniformHHLRotation d y *ᵥ Ket false))
  nlinarith [abs_nonneg (uniformHHLGamma d x - uniformHHLGamma d y)]

/-- If `x` is within `w ≤ d/32` of an eigenphase of magnitude in `[d, 1/4]`, its rotation is
unitary and its rotated zero state differs by at most `8*w/d`. -/
theorem uniform_hhl_clipped_rotation_and_local_continuity :
    ∀ (d lam x w : ℝ), 0 < d → d ≤ |lam| → |lam| ≤ 1 / 4 →
      0 < w → w ≤ d / 32 → |x - lam| ≤ w →
      uniformHHLRotation d x ∈ Matrix.unitaryGroup Bool ℂ ∧
        ‖toEuclidean_fromVec (uniformHHLRotation d x *ᵥ Ket false -
          uniformHHLRotation d lam *ᵥ Ket false)‖ ≤ 8 * w / d := by
  intro d lam x w hd hlam _ hw hwd hxl
  have htri : |lam| ≤ |x - lam| + |x| := by
    have ht := abs_add_le (lam - x) x
    rw [sub_add_cancel, abs_sub_comm] at ht
    exact ht
  have hx : d / 2 ≤ |x| := by linarith
  have hln : lam ≠ 0 := by intro h; subst lam; simp at hlam; linarith
  have hxn : x ≠ 0 := by intro h; subst x; simp at hx; linarith
  have hg : |uniformHHLGamma d x - uniformHHLGamma d lam| ≤ 4 * w / d := by
    rw [uniformHHLGamma_eq_reciprocal d x hd hx,
      uniformHHLGamma_eq_reciprocal d lam hd (by linarith)]
    have he : d / (4 * x) - d / (4 * lam) =
        d * (lam - x) / (4 * x * lam) := by field_simp
    rw [he, abs_div, abs_mul, abs_of_pos hd, abs_sub_comm lam x,
      abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    apply (div_le_iff₀ (by positivity : 0 < 4 * |x| * |lam|)).mpr
    have hlow := mul_le_mul hx hlam (by positivity) (by positivity)
    have hden : d * d ≤ 4 * |x| * |lam| := by nlinarith
    have hbound := mul_le_mul_of_nonneg_left hxl hd.le
    have hmult := mul_le_mul_of_nonneg_left hden (show 0 ≤ 4 * w / d by positivity)
    have he' : (4 * w / d) * (d * d) = 4 * w * d := by field_simp
    rw [he'] at hmult
    nlinarith
  refine ⟨uniformHHLRotation_unitary d x hd, ?_⟩
  calc
    _ ≤ 2 * |uniformHHLGamma d x - uniformHHLGamma d lam| :=
      uniformHHLRotation_vector_difference d x lam hd
    _ ≤ 2 * (4 * w / d) := mul_le_mul_of_nonneg_left hg (by norm_num)
    _ = _ := by ring

/-- A phase label within circular distance `w ≤ d/32` of a phase of magnitude in `[d, 1/4]`
decodes to a real value within `w`. -/
theorem uniformHHLDecode_good (M : ℕ) (y : Fin M) (lam d w : ℝ)
    (hM : 2 ≤ M) (hd : 0 < d) (hlam : d ≤ |lam|) (hlam' : |lam| ≤ 1 / 4)
    (hw : w ≤ d / 32)
    (hgood : phaseDistance lam ((y.val : ℝ) / (M : ℝ)) ≤ w) :
    |uniformHHLDecode M y - lam| ≤ w := by
  have hm : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hr0 : 0 ≤ (y.val : ℝ) / (M : ℝ) := by positivity
  have hr1 : (y.val : ℝ) / (M : ℝ) < 1 := by
    rw [div_lt_one hm]
    exact_mod_cast y.isLt
  have hl := abs_le.mp hlam'
  have hw' : w < 1 / 4 := by linarith
  let n : ℤ := ⌊lam - (y.val : ℝ) / (M : ℝ) + 1 / 2⌋
  have hg : |lam - (y.val : ℝ) / (M : ℝ) - (n : ℝ)| ≤ w := hgood
  have hg' := abs_le.mp hg
  unfold uniformHHLDecode
  split_ifs with hy
  · have hrhalf : (y.val : ℝ) / (M : ℝ) ≤ 1 / 2 := by
      apply (div_le_iff₀ hm).mpr
      have hh : (2 : ℝ) * y.val ≤ M := by exact_mod_cast hy
      linarith
    have hn0 : (-1 : ℝ) < n := by linarith
    have hn1 : (n : ℝ) < 1 := by linarith
    have hn : n = 0 := by
      have h0 : (-1 : ℤ) < n := by exact_mod_cast hn0
      have h1 : n < (1 : ℤ) := by exact_mod_cast hn1
      omega
    rw [hn, Int.cast_zero, sub_zero] at hg
    rwa [abs_sub_comm]
  · have hrhalf : 1 / 2 < (y.val : ℝ) / (M : ℝ) := by
      apply (lt_div_iff₀ hm).mpr
      have hh : (M : ℝ) < (2 : ℝ) * y.val := by exact_mod_cast (by omega : M < 2 * y.val)
      linarith
    have hn0 : (-2 : ℝ) < n := by linarith
    have hn1 : (n : ℝ) < 0 := by linarith
    have hn : n = -1 := by
      have h0 : (-2 : ℤ) < n := by exact_mod_cast hn0
      have h1 : n < (0 : ℤ) := by exact_mod_cast hn1
      omega
    rw [hn] at hg
    have he : (y.val : ℝ) / (M : ℝ) - 1 - lam =
        -(lam - (y.val : ℝ) / (M : ℝ) - ((-1 : ℤ) : ℝ)) := by push_cast; ring
    rw [he, abs_neg]
    exact hg

/-- For positive `M`, the squared amplitudes of the uniform phase-estimation kernel sum to one. -/
theorem uniform_qpeKernel_normalized (M : ℕ) (φ : ℝ) (hM : 0 < M) :
    ∑ y : Fin M, ‖qpeKernel M φ y‖ ^ 2 = 1 := by
  have hphase := (offgrid_phase_kernel_formula M φ (⟨0, hM⟩ : Fin M) hM).2.2
  exact normalized_applyGate (mem_unitaryGroup_adjoint (qftMatrix_unitary hM)) hphase

/-- For positive `d`, any two rotated zero-flag states have Euclidean distance at most two. -/
theorem uniformHHLRotation_vector_difference_le_two (d x y : ℝ) (hd : 0 < d) :
    ‖toEuclidean_fromVec (uniformHHLRotation d x *ᵥ Ket false -
      uniformHHLRotation d y *ᵥ Ket false)‖ ≤ 2 := by
  change ‖toEuclidean_fromVec (uniformHHLRotation d x *ᵥ Ket false) -
    toEuclidean_fromVec (uniformHHLRotation d y *ᵥ Ket false)‖ ≤ 2
  have hx := norm_applyGate_of_mem_unitaryGroup (uniformHHLRotation_unitary d x hd) (Ket false)
  have hy := norm_applyGate_of_mem_unitaryGroup (uniformHHLRotation_unitary d y hd) (Ket false)
  rw [norm_toEuclidean_fromVec_ket] at hx hy
  dsimp only [ApplyGate] at hx hy
  calc
    _ ≤ ‖toEuclidean_fromVec (uniformHHLRotation d x *ᵥ Ket false)‖ +
        ‖toEuclidean_fromVec (uniformHHLRotation d y *ᵥ Ket false)‖ := norm_sub_le _ _
    _ = 2 := by rw [hx, hy]; norm_num

/-- Under the stated spectral window and grid budget, the kernel-weighted squared error between
decoded and exact flag rotations is at most `η^2`. -/
theorem uniformHHL_spectral_window_error (M : ℕ) (lam d η : ℝ)
    (hM : 2 ≤ M) (hd : 0 < d) (hη : 0 < η) (hη1 : η ≤ 1)
    (hlam : d ≤ |lam|) (hlam' : |lam| ≤ 1 / 4)
    (hbudget : 4096 / (d ^ 2 * η ^ 4) ≤ (M : ℝ)) :
    (∑ y : Fin M, ‖qpeKernel M lam y‖ ^ 2 *
      ‖toEuclidean_fromVec (uniformHHLRotation d (uniformHHLDecode M y) *ᵥ Ket false -
        uniformHHLRotation d lam *ᵥ Ket false)‖ ^ 2) ≤ η ^ 2 := by
  let w := d * η / 32
  have hw : 0 < w := by dsimp [w]; positivity
  have hwd : w ≤ d / 32 := by dsimp [w]; nlinarith
  have hwhalf : w ≤ 1 / 2 := by linarith
  let bad := Finset.univ.filter (fun y : Fin M =>
    w < phaseDistance lam ((y.val : ℝ) / (M : ℝ)))
  have htail := uniform_phase_kernel_derived_tail M lam w hM hw hwhalf
  have hpoint (y : Fin M) :
      ‖qpeKernel M lam y‖ ^ 2 *
        ‖toEuclidean_fromVec (uniformHHLRotation d (uniformHHLDecode M y) *ᵥ Ket false -
          uniformHHLRotation d lam *ᵥ Ket false)‖ ^ 2 ≤
      ‖qpeKernel M lam y‖ ^ 2 * (η ^ 2 / 16) +
        (if w < phaseDistance lam ((y.val : ℝ) / (M : ℝ)) then
          4 * ‖qpeKernel M lam y‖ ^ 2 else 0) := by
    split_ifs with hy
    · have he := uniformHHLRotation_vector_difference_le_two d (uniformHHLDecode M y) lam hd
      have he2 := pow_le_pow_left₀ (norm_nonneg _) he 2
      have hb := mul_le_mul_of_nonneg_left he2 (sq_nonneg ‖qpeKernel M lam y‖)
      nlinarith [sq_nonneg η, mul_nonneg (sq_nonneg ‖qpeKernel M lam y‖) (sq_nonneg η)]
    · have hg := uniformHHLDecode_good M y lam d w hM hd hlam hlam' hwd (le_of_not_gt hy)
      have he := (uniform_hhl_clipped_rotation_and_local_continuity d lam
        (uniformHHLDecode M y) w hd hlam hlam' hw hwd hg).2
      have he' : 8 * w / d = η / 4 := by dsimp [w]; field_simp; ring
      rw [he'] at he
      have he2 := pow_le_pow_left₀ (norm_nonneg _) he 2
      have hb := mul_le_mul_of_nonneg_left he2 (sq_nonneg ‖qpeKernel M lam y‖)
      nlinarith
  have hsum := Finset.sum_le_sum (fun y (_ : y ∈ Finset.univ) => hpoint y)
  rw [Finset.sum_add_distrib, ← Finset.sum_mul,
    uniform_qpeKernel_normalized M lam (by omega), one_mul] at hsum
  have hbad : (∑ y : Fin M, if w < phaseDistance lam ((y.val : ℝ) / (M : ℝ))
      then 4 * ‖qpeKernel M lam y‖ ^ 2 else 0) =
      4 * ∑ y ∈ bad, ‖qpeKernel M lam y‖ ^ 2 := by
    rw [Finset.mul_sum]
    simp only [bad, Finset.sum_filter]
  rw [hbad] at hsum
  have htail' := mul_le_mul_of_nonneg_left htail (by norm_num : (0 : ℝ) ≤ 4)
  have hm : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hb : 4096 ≤ (M : ℝ) * (d ^ 2 * η ^ 4) :=
    (div_le_iff₀ (by positivity : 0 < d ^ 2 * η ^ 4)).mp hbudget
  have hwindow : 4 * (1 / (4 * (M : ℝ) * w ^ 2)) ≤ η ^ 2 / 4 := by
    calc
      _ = 1024 / ((M : ℝ) * d ^ 2 * η ^ 2) := by
        dsimp [w]
        field_simp
        ring
      _ ≤ η ^ 2 / 4 := by
        apply (div_le_iff₀ (by positivity : 0 < (M : ℝ) * d ^ 2 * η ^ 2)).mpr
        nlinarith only [hb]
  change 4 * ∑ y ∈ bad, ‖qpeKernel M lam y‖ ^ 2 ≤ _ at htail'
  nlinarith only [hsum, htail', hwindow, sq_nonneg η]

end Qatlib.Concepts.HhlAlgorithms.UniformHHL
