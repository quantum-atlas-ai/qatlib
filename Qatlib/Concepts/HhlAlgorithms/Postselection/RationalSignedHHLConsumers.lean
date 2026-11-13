/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.RationalProgram

/-!
# Signed rational HHL postselection

This module derives spectral formulas and least-squares postselection guarantees for
`rationalHHLRun` with signed, possibly zero eigenvalues. It also proves exact zero-mode behavior
and counts the arithmetic iterations used to build the rational rotation table, extending the
HHL setting of [HarrowHassidimLloyd2009].

## Main statements

* `rational_hhl_same_actual_least_squares_postselection`: success and normalized-direction
  estimates for the actual rational run.
* `rationalHHL_zero_mode`: a zero eigenmode retains zero phase and false flags.
* `rational_hhl_exact_zero_range_branch`: inputs supported on the kernel have zero success
  probability.

## References

* [Harrow et al., 2009][HarrowHassidimLloyd2009]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.NativeNumerics.LayeredMean
open Qatlib.Concepts.QlsReadoutSpec.LowRankHHL
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.HhlAlgorithms.GridExactHHL
open Qatlib.Concepts.HhlAlgorithms.RationalProgram
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram
open Qatlib.Concepts.HhlAlgorithms.UniformHHL
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Concepts.MonteCarloMean.PayoffRotation

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
namespace Qatlib.Concepts.HhlAlgorithms.Postselection
open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- For the signed low-rank spectral promise and sufficient grid size, an error `e = eta + 32 /
2^k < d * tau` gives success probability at least `(d * tau - e)^2` and postselected
least-squares direction error at most `2 * e / (d * tau)`. -/
theorem rational_hhl_same_actual_least_squares_postselection :
    ∀ (D M k : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D) (d : ℚ) (eta : ℝ),
      V ∈ Matrix.unitaryGroup (Fin D) ℂ → B ∈ Matrix.unitaryGroup (Fin D) ℂ → 0 < d →
      0 < eta → eta ≤ 1 → (∀ i, eig i=0 ∨ ((d:ℝ) ≤ |eig i| ∧ |eig i| ≤ 1/4)) →
      4096/((d:ℝ)^2*eta^4) ≤ (M:ℝ) →
      let tau := leastSquaresOverlap (continuousHHLMatrix eig V) (B*ᵥ Ket j)
      let e := eta+32/2^k
      let out := rationalHHLRun M hM (continuousHHLOracle eig V) d k B j
      e < (d:ℝ)*tau →
      ((d:ℝ)*tau-e)^2 ≤ MeasureProb out (flagSuccessSet D M) ∧
      ‖toEuclidean_fromVec (PostMeasure out (flagSuccessSet D M) -
        uniformHHLSolutionTarget M hM eig V B j)‖ ≤ 2*e/((d:ℝ)*tau) := by
  intro D M k hM eig V B j d eta hV hB hd heta heta1 heig hbudget
  (try dsimp only)
  intro hgap
  have h := lowRank_output_from_error hM eig V B j d (eta+32/2^k) hV
    (by exact_mod_cast hd) (by positivity) heig
    (rationalHHLRun M hM (continuousHHLOracle eig V) d k B j)
    (rational_hhl_low_rank_full_program_error D M k hM eig V B j d eta
      hV hB hd heta heta1 heig hbudget) hgap
  exact ⟨h.1, h.2.2⟩

/-- On a product input with a false flag, the rational HHL flag gate multiplies each phase
amplitude by the corresponding rotation entry and leaves the data factor unchanged. -/
theorem rationalHHLFlag_product {D M : ℕ} (d : ℚ) (k : ℕ)
    (a : QState (Fin M)) (v : QState (Fin D)) :
    ApplyGate (rationalHHLFlag (D := D) (M := M) d k)
      (TensorState a (TensorState (Ket false) v)) =
    fun p => a p.1 * (rationalHHLRotation d (rationalHHLDecode M p.1) k p.2.1 false) * v p.2.2 := by
  funext p
  rcases p with ⟨y,f,i⟩
  simp [ApplyGate, rationalHHLFlag, relabelGate, gridHHLFlagData, Matrix.mulVec,
    dotProduct, TensorGate, BlockDiag, TensorState, Ket, Fintype.sum_prod_type,
    Matrix.one_apply, mul_assoc, mul_comm, mul_left_comm]

/-- The rational HHL flag gate fixes a state with zero phase label and a false flag. -/
theorem rationalHHL_zero_flag {D M : ℕ} (hM : 0 < M) (d : ℚ) (k : ℕ) (v : QState (Fin D)) :
    rationalHHLFlag (D := D) (M := M) d k *ᵥ
      TensorState (Ket (⟨0,hM⟩ : Fin M)) (TensorState (Ket false) v) =
      TensorState (Ket (⟨0,hM⟩ : Fin M)) (TensorState (Ket false) v) := by
  change ApplyGate _ _ = _
  rw [rationalHHLFlag_product]
  funext p
  rcases p with ⟨y,f,i⟩
  by_cases hy : y=(⟨0,hM⟩ : Fin M)
  · subst y
    simp [rationalHHLDecode, rationalHHLRotation_zero, TensorState, Ket, Matrix.one_apply]
  · simp [TensorState, Ket, hy]

/-- Running rational HHL on a zero eigenmode returns that eigenvector with zero phase and both
flags false. -/
theorem rationalHHL_zero_mode {D M : ℕ} (hM : 2 ≤ M) (eig : Fin D → ℝ)
    (V : Operator D) (i : Fin D) (d : ℚ) (k : ℕ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hi : eig i=0) :
    rationalHHLRun M hM (continuousHHLOracle eig V) d k V i =
      TensorState (Ket (⟨0,by omega⟩ : Fin M))
        (TensorState (Ket false) (TensorState (Ket false) (V*ᵥ Ket i))) := by
  have hMp : 0 < M := by omega
  let U := continuousHHLOracle eig V
  let F := gridHHLBlockOp (D := D) (M := M) U
  let a := TensorState (Ket (⟨0,hMp⟩ : Fin M)) (TensorState (Ket false) (V*ᵥ Ket i))
  have hU := continuous_hhl_oracle_unitary eig V hV
  have hF := gridHHLBlockOp_unitary hMp U hU
  have hstar : Fᴴ*F=1 := by
    simpa only [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] using! hF
  have hfwd : F*ᵥ a=a := by
    simpa only [run_qpeBlock_eq] using! lowRank_zero_forward hMp eig V hV i hi
  have hback : Fᴴ*ᵥ a=a := by
    calc
      _ = Fᴴ*ᵥ (F*ᵥ a) := congrArg (fun x => Fᴴ*ᵥ x) hfwd.symm
      _ = a := by rw [Matrix.mulVec_mulVec, hstar, Matrix.one_mulVec]
  have hrun : rationalHHLRun M hM U d k V i = phaseFlagEmbed M a := by
    rw [rationalHHLRun_eq M hM U hU d k V i, run_append, run_append, run_gate, run_nil]
    simp only [ApplyGate]
    change phaseFlagEmbed M (Run 1 (gridHHLQPEBlockInv U)
      (rationalHHLFlag d k *ᵥ (Run 1 (gridHHLQPEBlock U) a))) = phaseFlagEmbed M a
    rw [run_qpeBlock_eq, hfwd, rationalHHL_zero_flag hMp d k, run_qpeBlockInv_eq]
    exact congrArg (phaseFlagEmbed M) hback
  rw [hrun]
  funext p
  rcases p with ⟨y,s,f,i⟩
  cases s <;> simp [a, phaseFlagEmbed, TensorState, Ket]

/-- The rational HHL output is the phase-flag embedding of preparation followed by QPE, the
rational flag rotation, and inverse QPE. -/
theorem rationalHHL_run_formula {D M : ℕ} (hM : 2 ≤ M) (eig : Fin D → ℝ)
    (V : Operator D) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (d : ℚ) (k : ℕ) (B : Operator D) (j : Fin D) :
    rationalHHLRun M hM (continuousHHLOracle eig V) d k B j =
      phaseFlagEmbed M ((gridHHLBlockOp (D := D) (M := M) (continuousHHLOracle eig V))ᴴ *ᵥ
        (rationalHHLFlag d k *ᵥ (gridHHLBlockOp (D := D) (M := M) (continuousHHLOracle eig V) *ᵥ
          TensorState (Ket (⟨0,by omega⟩ : Fin M)) (TensorState (Ket false) (B *ᵥ Ket j))))) := by
  rw [rationalHHLRun_eq M hM _ (continuous_hhl_oracle_unitary eig V hV),
    run_append, run_append, run_gate, run_nil, run_qpeBlock_eq, run_qpeBlockInv_eq]
  rfl

/-- The rational HHL output decomposes into eigenmode runs with coefficients given by the
prepared input in the eigenbasis. -/
theorem rationalHHL_actual_spectral {D M : ℕ} (hM : 2 ≤ M) (eig : Fin D → ℝ)
    (V B : Operator D) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (d : ℚ) (k : ℕ) (j : Fin D) :
    rationalHHLRun M hM (continuousHHLOracle eig V) d k B j =
      ∑ i : Fin D, (Vᴴ *ᵥ (B *ᵥ Ket j)) i •
        rationalHHLRun M hM (continuousHHLOracle eig V) d k V i := by
  let beta := Vᴴ *ᵥ (B *ᵥ Ket j)
  have hi : TensorState (Ket (⟨0,by omega⟩ : Fin M)) (TensorState (Ket false) (B *ᵥ Ket j)) =
      ∑ i : Fin D, beta i • TensorState (Ket (⟨0,by omega⟩ : Fin M))
        (TensorState (Ket false) (V *ᵥ Ket i)) := by
    rw [gridHHL_eigen_expansion (M := M) V hV (B *ᵥ Ket j)]
    funext p
    simp only [TensorState, Fintype.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i h
    ring
  rw [rationalHHL_run_formula hM eig V hV d k B j, hi]
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul]
  have hp : ∀ (vs : Fin D → QState (Fin M × (Bool × Fin D))),
      phaseFlagEmbed M (∑ i, beta i • vs i) = ∑ i, beta i • phaseFlagEmbed M (vs i) := by
    intro vs
    funext p
    rcases p with ⟨y,s,r⟩
    cases s <;> simp [phaseFlagEmbed, Pi.smul_apply]
  rw [hp]
  apply Finset.sum_congr rfl
  intro i h
  rw [rationalHHL_run_formula hM eig V hV d k V i]

/-- If the prepared input has no component in any nonzero eigenspace, the rational HHL success
probability is exactly zero. -/
theorem rational_hhl_exact_zero_range_branch :
    ∀ (D M k : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D) (d : ℚ),
      V ∈ Matrix.unitaryGroup (Fin D) ℂ → B ∈ Matrix.unitaryGroup (Fin D) ℂ → 0 < d →
      (∀ i, eig i ≠ 0 → (Vᴴ*ᵥ (B*ᵥ Ket j)) i=0) →
      MeasureProb (rationalHHLRun M hM (continuousHHLOracle eig V) d k B j) (flagSuccessSet D M)=0 := by
  intro D M k hM eig V B j d hV _hB _hd hzero
  unfold MeasureProb BornProb
  apply Finset.sum_eq_zero
  intro p hp
  have hf : p.2.2.1=true := (Finset.mem_filter.mp hp).2
  have hout : rationalHHLRun M hM (continuousHHLOracle eig V) d k B j p=0 := by
    rw [rationalHHL_actual_spectral hM eig V B hV d k j]
    simp only [Fintype.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro i _hi
    by_cases hz : eig i=0
    · rw [rationalHHL_zero_mode hM eig V i d k hV hz]
      simp [TensorState, Ket, hf]
    · rw [hzero i hz, zero_mul]
  rw [hout]; simp

/-- Under the stated precision assumptions, the rational HHL table has `M` entries and its
square-root bracket computations total exactly `2 * M * k` iterations. -/
theorem rational_hhl_paid_table_arithmetic_and_precision :
    ∀ (M k : ℕ) (d : ℚ) (eta : ℝ), 0 < d → 0 < eta → 32/(2:ℝ)^k ≤ eta →
      (rationalHHLTable M d k).size=M ∧
      (∑ y : Fin M, ((rationalSqrtBracket ((rationalHHLGamma d (rationalHHLDecode M y))^2) k).2.2+
        (rationalSqrtBracket (1-(rationalHHLGamma d (rationalHHLDecode M y))^2) k).2.2))=2*M*k := by
  intro M k d _eta hd _heta _hprecision
  refine ⟨rationalHHLTable_size M d k, ?_⟩
  have hc (y : Fin M) :
      (rationalSqrtBracket ((rationalHHLGamma d (rationalHHLDecode M y))^2) k).2.2=k ∧
      (rationalSqrtBracket (1-(rationalHHLGamma d (rationalHHLDecode M y))^2) k).2.2=k := by
    obtain ⟨hq, hq1⟩ := rationalHHLGamma_sq_range d (rationalHHLDecode M y) hd
    exact ⟨(rational_sqrt_bracket_actual_interval_and_comparisons _ k hq hq1).2.2.2.2.2.2.1,
      (rational_sqrt_bracket_actual_interval_and_comparisons _ k (by linarith) (by linarith)).2.2.2.2.2.2.1⟩
  simp only [(hc _).1, (hc _).2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring
end Qatlib.Concepts.HhlAlgorithms.Postselection
