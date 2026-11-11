/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpMmwSolver.OracleError.SdpResidualMacros
import Qatlib.Concepts.HspRecovery.SieveLaw.NormalizedBranchDistance
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Tactic.Linarith

/-!
# Trace distance bounds for commuting Gibbs operators

`sdpGibbsNormalizationBound` bounds the trace distance between normalized positive matrix
exponentials by their unnormalized difference and trace mismatch.
`sdpGibbsPerturbationCommuting` specializes to commuting Hermitian exponents and gives the bound
2(exp(‖H − H'‖) − 1).

For the mathematical background, see [BrandaoSvore2017].

## Main statements

* `sdpGibbsPerturbationCommuting`: For commuting Hermitian exponents with positive traces and
  positive semidefinite exponentials, the normalized Gibbs trace distance is at most 2(exp(‖H −
  H'‖) − 1). See [BrandaoSvore2017].

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.HspRecovery.SieveLaw

namespace Qatlib.Concepts.SdpMmwSolver.OracleError
open scoped Matrix.Norms.L2Operator ComplexOrder CStarAlgebra
set_option warningAsError false

/-- Bounds the trace distance between normalized positive exponentials by the sum of their
trace-norm difference and absolute trace difference, divided by the larger positive trace. -/
theorem sdpGibbsNormalizationBound (D : ℕ) (H H' : Operator D)
    (hX : (NormedSpace.exp H).PosSemidef) (hY : (NormedSpace.exp H').PosSemidef)
    (hp : 0 < (Matrix.trace (NormedSpace.exp H)).re)
    (hq : 0 < (Matrix.trace (NormedSpace.exp H')).re) :
    Matrix.traceNorm
      (((Matrix.trace (NormedSpace.exp H)).re : ℂ)⁻¹ • NormedSpace.exp H -
        ((Matrix.trace (NormedSpace.exp H')).re : ℂ)⁻¹ • NormedSpace.exp H') ≤
      (Matrix.traceNorm (NormedSpace.exp H - NormedSpace.exp H') +
        |(Matrix.trace (NormedSpace.exp H)).re - (Matrix.trace (NormedSpace.exp H')).re|) /
        max (Matrix.trace (NormedSpace.exp H)).re (Matrix.trace (NormedSpace.exp H')).re := by
  simpa only [normalizedPositiveBranch, if_pos hp, if_pos hq, Complex.ofReal_inv] using!
    normalized_positive_branch_distance (Fin D) (NormedSpace.exp H) (NormedSpace.exp H')
      hX hY hp hq

/-- For a Hermitian operator on a positive-dimensional space, the operator norm of exp(E) − 1 is
at most exp(‖E‖) − 1. -/
theorem sdpHermitianExpSubOneNorm (D : ℕ) (E : Operator D) (hD : 0 < D) (hE : E.IsHermitian) :
    ‖NormedSpace.exp E - 1‖ ≤ Real.exp ‖E‖ - 1 := by
  letI : Nonempty (Fin D) := ⟨⟨0,hD⟩⟩
  letI : CStarAlgebra (Operator D) := {}
  have he : cfc (fun x : ℝ => Real.exp x - 1) E = NormedSpace.exp E - 1 := by
    rw [cfc_sub (f := Real.exp) (g := fun _ : ℝ => 1) E, cfc_const_one ℝ E,
      CFC.real_exp_eq_normedSpace_exp hE]
  rw [← he]
  apply norm_cfc_le (sub_nonneg.mpr (Real.one_le_exp_iff.mpr (norm_nonneg E)))
  intro x hx
  have hb : |x| ≤ ‖E‖ := by
    simpa only [Real.norm_eq_abs] using! spectrum.norm_le_norm_of_mem hx
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · have hlo : Real.exp (-‖E‖) ≤ Real.exp x := Real.exp_le_exp.mpr (abs_le.mp hb).1
    linarith [Real.add_one_le_exp ‖E‖, Real.add_one_le_exp (-‖E‖)]
  · have hhi : Real.exp x ≤ Real.exp ‖E‖ := Real.exp_le_exp.mpr (abs_le.mp hb).2
    linarith

/-- For commuting Hermitian exponents with positive traces and positive semidefinite
exponentials, the normalized Gibbs trace distance is at most 2(exp(‖H − H'‖) − 1). See
[BrandaoSvore2017]. -/
theorem sdpGibbsPerturbationCommuting (D : ℕ) (H H' : Operator D)
    (hD : 0 < D) (hH : H.IsHermitian) (hH' : H'.IsHermitian) (hc : Commute H H')
    (hX : (NormedSpace.exp H).PosSemidef) (hY : (NormedSpace.exp H').PosSemidef)
    (hp : 0 < (Matrix.trace (NormedSpace.exp H)).re)
    (hq : 0 < (Matrix.trace (NormedSpace.exp H')).re) :
    Matrix.traceNorm
      (((Matrix.trace (NormedSpace.exp H)).re : ℂ)⁻¹ • NormedSpace.exp H -
        ((Matrix.trace (NormedSpace.exp H')).re : ℂ)⁻¹ • NormedSpace.exp H') ≤
      2 * (Real.exp ‖H - H'‖ - 1) := by
  let c := Real.exp ‖H - H'‖ - 1
  have hc0 : 0 ≤ c := sub_nonneg.mpr (Real.one_le_exp_iff.mpr (norm_nonneg _))
  have hexp : NormedSpace.exp H = NormedSpace.exp (H - H') * NormedSpace.exp H' := by
    simpa only [sub_add_cancel] using!
      Matrix.exp_add_of_commute (H-H') H' (hc.sub_left (Commute.refl H'))
  have hsub : NormedSpace.exp H - NormedSpace.exp H' =
      (NormedSpace.exp (H-H') - 1) * NormedSpace.exp H' := by
    rw [hexp, sub_mul, one_mul]
  have hraw : Matrix.traceNorm (NormedSpace.exp H - NormedSpace.exp H') ≤
      c * (Matrix.trace (NormedSpace.exp H')).re := by
    rw [hsub]
    apply (Matrix.traceNorm_mul_le_opNorm_traceNorm _ _).trans
    rw [posSemidef_traceNorm_eq_re hY]
    exact mul_le_mul_of_nonneg_right (sdpHermitianExpSubOneNorm D (H-H') hD (hH.sub hH')) hq.le
  have hmass : |(Matrix.trace (NormedSpace.exp H)).re -
      (Matrix.trace (NormedSpace.exp H')).re| ≤
      Matrix.traceNorm (NormedSpace.exp H - NormedSpace.exp H') := by
    rw [← Complex.sub_re, ← Matrix.trace_sub]
    exact (Complex.abs_re_le_norm _).trans (Matrix.abs_trace_le_traceNorm _)
  apply (sdpGibbsNormalizationBound D H H' hX hY hp hq).trans
  apply (div_le_iff₀ (lt_max_of_lt_left hp)).mpr
  have hrmax := mul_le_mul_of_nonneg_left
    (le_max_right (Matrix.trace (NormedSpace.exp H)).re
      (Matrix.trace (NormedSpace.exp H')).re) hc0
  dsimp [c] at hraw hrmax
  nlinarith

end Qatlib.Concepts.SdpMmwSolver.OracleError
