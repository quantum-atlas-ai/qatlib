/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpMmwSolver.OracleError.SdpGibbsPerturbation
import Qatlib.Concepts.MatrixExpTrace.ExpPerturbation
import Qatlib.Concepts.HspRecovery.SieveLaw.NormalizedBranchDistance

/-!
# Perturbation bounds for normalized Gibbs matrices

This module transfers the trace-norm perturbation bound for Hermitian exponentials to their
normalized Gibbs matrices. `normalized_gibbs_branch_traceNorm_le` supplies positivity, positive
partition functions, and a normalized trace-norm bound, while `normalized_gibbs_branch_eps_le`
turns a logarithmic operator-norm tolerance into a prescribed error.

`sdp_gibbs_perturbation_noncommuting` states the same estimate in the operator representation
used by semidefinite-programming routines. The matrix positivity background is standard
[Bhatia1997], and Gibbs-state approximation is a component of the SDP framework in
[BrandaoSvore2017].

## Main statements

- `exp_posSemidef` and `exp_trace_re_pos` establish the positivity needed for normalization.
* `normalized_gibbs_branch_traceNorm_le` bounds normalized trace-norm distance by `2 * (exp ‖H -
  K‖ - 1)`.
- `normalized_gibbs_branch_eps_le` gives an error tolerance under `‖H - K‖ ≤ log (1 + ε / 2)`.
- `normalized_gibbs_completion` packages the branch, tolerance, and SDP formulations.

## References

- [Bhatia, 1997][Bhatia1997]. Matrix Analysis.
* [Brandao and Svore, 2017][BrandaoSvore2017]. Quantum Speed-Ups for Solving Semidefinite
  Programs.
-/

open Qatlib.Concepts.MatrixExpTrace.ExpPerturbation
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SdpMmwSolver.OracleError
open Qatlib.Concepts.HspRecovery.SieveLaw

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Qatlib.Concepts.MatrixExpTrace.GibbsNorm

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

/-- The matrix exponential of a Hermitian matrix is positive semidefinite. -/
theorem exp_posSemidef {I : Type} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (hH : H.IsHermitian) :
    (NormedSpace.exp H).PosSemidef := by
  let Hm : HermitianMat I ℂ := ⟨H, hH⟩
  have h : Hm.exp.mat.PosSemidef := HermitianMat.zero_le_iff.mp Hm.exp_nonneg
  simpa only [hermitian_exp_mat] using! h

/-- The real trace of a Hermitian matrix exponential is strictly positive when the matrix index
type is nonempty. -/
theorem exp_trace_re_pos {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (H : Matrix I I ℂ) (hH : H.IsHermitian) :
    0 < (Matrix.trace (NormedSpace.exp H)).re :=
  exp_trace_pos ⟨H, hH⟩

/-- Establishes positivity and positive real traces for the Hermitian exponentials of `H` and
`K`, and bounds the trace-norm distance of their normalized positive branches by `2 * (exp
‖H - K‖ - 1)`. -/
theorem normalized_gibbs_branch_traceNorm_le {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (H K : Matrix I I ℂ) (hH : H.IsHermitian) (hK : H.IsHermitian → K.IsHermitian) :
    (NormedSpace.exp H).PosSemidef ∧ (NormedSpace.exp K).PosSemidef ∧
    0 < (Matrix.trace (NormedSpace.exp H)).re ∧
    0 < (Matrix.trace (NormedSpace.exp K)).re ∧
    Matrix.traceNorm
      (Qatlib.Concepts.HspRecovery.SieveLaw.normalizedPositiveBranch (NormedSpace.exp H) -
       Qatlib.Concepts.HspRecovery.SieveLaw.normalizedPositiveBranch (NormedSpace.exp K)) ≤
      2 * (Real.exp ‖H - K‖ - 1) := by
  have hK' : K.IsHermitian := hK hH
  have hX : (NormedSpace.exp H).PosSemidef := exp_posSemidef H hH
  have hY : (NormedSpace.exp K).PosSemidef := exp_posSemidef K hK'
  have hp : 0 < (Matrix.trace (NormedSpace.exp H)).re := exp_trace_re_pos H hH
  have hq : 0 < (Matrix.trace (NormedSpace.exp K)).re := exp_trace_re_pos K hK'
  refine ⟨hX, hY, hp, hq, ?_⟩
  have hraw : Matrix.traceNorm (NormedSpace.exp H - NormedSpace.exp K) ≤
      (Real.exp ‖H - K‖ - 1) * (Matrix.trace (NormedSpace.exp H)).re :=
    noncommuting_exp_trace_norm I H K hH hK'
  have hmass : |(Matrix.trace (NormedSpace.exp H)).re -
      (Matrix.trace (NormedSpace.exp K)).re| ≤
      Matrix.traceNorm (NormedSpace.exp H - NormedSpace.exp K) := by
    rw [← Complex.sub_re, ← Matrix.trace_sub]
    exact (Complex.abs_re_le_norm _).trans (Matrix.abs_trace_le_traceNorm _)
  have hc0 : 0 ≤ Real.exp ‖H - K‖ - 1 :=
    sub_nonneg.mpr (Real.one_le_exp (norm_nonneg (H - K)))
  have hmax : (Matrix.trace (NormedSpace.exp H)).re ≤
      max (Matrix.trace (NormedSpace.exp H)).re (Matrix.trace (NormedSpace.exp K)).re :=
    le_max_left _ _
  have hrmax : (Real.exp ‖H - K‖ - 1) * (Matrix.trace (NormedSpace.exp H)).re ≤
      (Real.exp ‖H - K‖ - 1) *
        max (Matrix.trace (NormedSpace.exp H)).re (Matrix.trace (NormedSpace.exp K)).re :=
    mul_le_mul_of_nonneg_left hmax hc0
  apply (Qatlib.Concepts.HspRecovery.SieveLaw.normalized_positive_branch_distance I
    (NormedSpace.exp H) (NormedSpace.exp K) hX hY hp hq).trans
  apply (div_le_iff₀ (lt_max_of_lt_left hp)).mpr
  linarith

/-- For Hermitian inputs, an operator-norm perturbation at most `log (1 + ε / 2)` implies that
their normalized Gibbs branches have trace-norm distance at most the positive tolerance `ε`. -/
theorem normalized_gibbs_branch_eps_le (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    (H K : Matrix I I ℂ) (ε : ℝ)
    (hH : H.IsHermitian) (hK : K.IsHermitian) (hε : 0 < ε)
    (hδ : ‖H - K‖ ≤ Real.log (1 + ε / 2)) :
    Matrix.traceNorm
      (Qatlib.Concepts.HspRecovery.SieveLaw.normalizedPositiveBranch (NormedSpace.exp H) -
       Qatlib.Concepts.HspRecovery.SieveLaw.normalizedPositiveBranch (NormedSpace.exp K)) ≤ ε := by
  have hbase := (normalized_gibbs_branch_traceNorm_le H K hH (fun _ => hK)).2.2.2.2
  have h1 : 0 < 1 + ε / 2 := by linarith
  have hexp : Real.exp ‖H - K‖ ≤ 1 + ε / 2 := by
    calc
      Real.exp ‖H - K‖ ≤ Real.exp (Real.log (1 + ε / 2)) := Real.exp_le_exp.mpr hδ
      _ = 1 + ε / 2 := Real.exp_log h1
  linarith

/-- For positive dimension and Hermitian `H` and `K`, bounds the trace-norm distance between
`exp H / re (trace (exp H))` and its `K` counterpart by `2 * (exp ‖H - K‖ - 1)`. -/
theorem sdp_gibbs_perturbation_noncommuting (D : ℕ) (H K : Qatlib.Foundations.PureStateMath.Operator D)
    (hD : 0 < D) (hH : H.IsHermitian) (hK : K.IsHermitian) :
    Matrix.traceNorm
      (((Matrix.trace (NormedSpace.exp H)).re : ℂ)⁻¹ • NormedSpace.exp H -
       ((Matrix.trace (NormedSpace.exp K)).re : ℂ)⁻¹ • NormedSpace.exp K) ≤
      2 * (Real.exp ‖H - K‖ - 1) := by
  letI : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  have hX : (NormedSpace.exp H).PosSemidef := exp_posSemidef H hH
  have hY : (NormedSpace.exp K).PosSemidef := exp_posSemidef K hK
  have hp : 0 < (Matrix.trace (NormedSpace.exp H)).re := exp_trace_re_pos H hH
  have hq : 0 < (Matrix.trace (NormedSpace.exp K)).re := exp_trace_re_pos K hK
  have hraw : Matrix.traceNorm (NormedSpace.exp H - NormedSpace.exp K) ≤
      (Real.exp ‖H - K‖ - 1) * (Matrix.trace (NormedSpace.exp H)).re :=
    noncommuting_exp_trace_norm (Fin D) H K hH hK
  have hmass : |(Matrix.trace (NormedSpace.exp H)).re -
      (Matrix.trace (NormedSpace.exp K)).re| ≤
      Matrix.traceNorm (NormedSpace.exp H - NormedSpace.exp K) := by
    rw [← Complex.sub_re, ← Matrix.trace_sub]
    exact (Complex.abs_re_le_norm _).trans (Matrix.abs_trace_le_traceNorm _)
  have hc0 : 0 ≤ Real.exp ‖H - K‖ - 1 :=
    sub_nonneg.mpr (Real.one_le_exp (norm_nonneg (H - K)))
  have hmax : (Matrix.trace (NormedSpace.exp H)).re ≤
      max (Matrix.trace (NormedSpace.exp H)).re (Matrix.trace (NormedSpace.exp K)).re :=
    le_max_left _ _
  have hrmax : (Real.exp ‖H - K‖ - 1) * (Matrix.trace (NormedSpace.exp H)).re ≤
      (Real.exp ‖H - K‖ - 1) *
        max (Matrix.trace (NormedSpace.exp H)).re (Matrix.trace (NormedSpace.exp K)).re :=
    mul_le_mul_of_nonneg_left hmax hc0
  apply (Qatlib.Concepts.SdpMmwSolver.OracleError.sdpGibbsNormalizationBound
    D H K hX hY hp hq).trans
  apply (div_le_iff₀ (lt_max_of_lt_left hp)).mpr
  linarith

/-- Packages the normalized Gibbs perturbation bound with its positivity guarantees, the
logarithmic tolerance criterion, and the equivalent formula using explicitly normalized SDP
operators. -/
theorem normalized_gibbs_completion :
    (∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
        (H K : Matrix I I ℂ), H.IsHermitian → K.IsHermitian →
      (NormedSpace.exp H).PosSemidef ∧ (NormedSpace.exp K).PosSemidef ∧
      0 < (Matrix.trace (NormedSpace.exp H)).re ∧
      0 < (Matrix.trace (NormedSpace.exp K)).re ∧
      Matrix.traceNorm
        (Qatlib.Concepts.HspRecovery.SieveLaw.normalizedPositiveBranch (NormedSpace.exp H) -
         Qatlib.Concepts.HspRecovery.SieveLaw.normalizedPositiveBranch (NormedSpace.exp K)) ≤
        2 * (Real.exp ‖H - K‖ - 1)) ∧
    (∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
        (H K : Matrix I I ℂ) (ε : ℝ),
      H.IsHermitian → K.IsHermitian → 0 < ε →
      ‖H - K‖ ≤ Real.log (1 + ε / 2) →
      Matrix.traceNorm
        (Qatlib.Concepts.HspRecovery.SieveLaw.normalizedPositiveBranch (NormedSpace.exp H) -
         Qatlib.Concepts.HspRecovery.SieveLaw.normalizedPositiveBranch (NormedSpace.exp K)) ≤ ε) ∧
    (∀ (D : ℕ) (H K : Qatlib.Foundations.PureStateMath.Operator D),
      0 < D → H.IsHermitian → K.IsHermitian →
      Matrix.traceNorm
        (((Matrix.trace (NormedSpace.exp H)).re : ℂ)⁻¹ • NormedSpace.exp H -
         ((Matrix.trace (NormedSpace.exp K)).re : ℂ)⁻¹ • NormedSpace.exp K) ≤
        2 * (Real.exp ‖H - K‖ - 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro I _ _ _ H K hH hK
    exact normalized_gibbs_branch_traceNorm_le H K hH (fun _ => hK)
  · intro I _ _ _ H K ε hH hK hε hδ
    exact normalized_gibbs_branch_eps_le I H K ε hH hK hε hδ
  · intro D H K hD hH hK
    exact sdp_gibbs_perturbation_noncommuting D H K hD hH hK

end Qatlib.Concepts.MatrixExpTrace.GibbsNorm
