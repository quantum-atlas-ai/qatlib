/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.DifferenceError.CentralDifferenceDirectionalErrorStat
import Qatlib.Concepts.GradientOracle.DifferenceError.CentralDifferenceOneDimErrorOpti
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Directional central-difference error

`centralDifferenceDirectionalError` derives the multidimensional error estimate by restricting a
smooth function to the line in the given nonzero direction. A bound on its normalized
directional derivative of order `2 * m + 1` controls the difference from the derivative at zero.
See [GilyenArunachalamWiebe2019] for background.

## Main statements

* `centralDifferenceDirectionalError`: For a nonzero direction and the stated smoothness and
  normalized directional-derivative bound, the central-difference error is at most `B * exp (-(1
  / 2) * m) * ‖x‖ ^ (2 * m + 1)`.

## References

* [Gilyen, Arunachalam, and Wiebe, 2019][GilyenArunachalamWiebe2019]
-/

set_option warningAsError false
open Qatlib.Concepts.GradientOracle.CentralDiff

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Qatlib.Concepts.GradientOracle.DifferenceError
open scoped Classical BigOperators

/-- For a nonzero direction and the stated smoothness and normalized directional-derivative
bound, the central-difference error is at most `B * exp (-(1 / 2) * m) * ‖x‖ ^ (2 * m + 1)`. -/
theorem centralDifferenceDirectionalError : CentralDifferenceDirectionalError := by
  intro d m hm B f hf x hx hbound
  let L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin d) := (ContinuousLinearMap.id ℝ ℝ).smulRight x
  let g : ℝ → ℝ := f ∘ L
  have hg : ContDiff ℝ (2*m+1) g := hf.comp L.contDiff
  have hL (τ : ℝ) : L τ=τ • x := rfl
  have he (τ : ℝ) : iteratedDeriv (2*m+1) g τ=
      iteratedFDeriv ℝ (2*m+1) f (τ • x) (fun _ : Fin (2*m+1) => x) := by
    rw [iteratedDeriv_eq_iteratedFDeriv,L.iteratedFDeriv_comp_right hf τ le_rfl]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,hL,one_smul]
  have hn : ‖x‖≠0 := norm_ne_zero_iff.mpr hx
  have hxx : ‖x‖ • ((‖x‖⁻¹ : ℝ) • x)=x := by rw [smul_smul,mul_inv_cancel₀ hn,one_smul]
  have hscale (τ : ℝ) : iteratedFDeriv ℝ (2*m+1) f (τ • x) (fun _ : Fin (2*m+1) => x)=
      ‖x‖^(2*m+1)*iteratedFDeriv ℝ (2*m+1) f (τ • x)
        (fun _ : Fin (2*m+1) => (‖x‖⁻¹ : ℝ) • x) := by
    have h := (iteratedFDeriv ℝ (2*m+1) f (τ • x)).map_smul_univ
      (fun _ : Fin (2*m+1) => ‖x‖) (fun _ : Fin (2*m+1) => (‖x‖⁻¹ : ℝ) • x)
    simpa only [hxx,Finset.prod_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] using h
  have hb (τ : ℝ) (hτ : τ∈Set.Icc (-(m : ℝ)*1) ((m : ℝ)*1)) :
      |iteratedDeriv (2*m+1) g τ|≤B*‖x‖^(2*m+1) := by
    rw [he,hscale,abs_mul,abs_of_nonneg (pow_nonneg (norm_nonneg x) (2*m+1))]
    have h :=
        mul_le_mul_of_nonneg_left (hbound τ (by simpa only [mul_one] using hτ))
        (pow_nonneg (norm_nonneg x) (2*m+1))
    simpa only [mul_comm] using h
  have hfirst : deriv g 0=(fderiv ℝ f 0) x := by
    have hd : HasFDerivAt f (fderiv ℝ f 0) (L 0) :=
      by
        simpa only [map_zero] using (hf.differentiable (by norm_num) (L 0)).hasFDerivAt
    have h := (hd.comp 0 L.hasFDerivAt).hasDerivAt
    simpa only [L,map_zero,ContinuousLinearMap.comp_apply,ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.id_apply,one_smul] using h.deriv
  have h := centralDifferenceOneDimError m hm 1 (B*‖x‖^(2*m+1)) (by norm_num) g hg hb
  rw [hfirst] at h
  change _≤_ at h
  simp only [mul_one,abs_one,one_pow] at h
  have hsum : (∑ l∈Finset.Ico (-(m : ℤ)) ((m : ℤ)+1),centralDiffCoeff m l*g (l : ℝ))=
      centralDiffApply m f x := rfl
  rw [hsum,abs_sub_comm] at h
  convert h using 1
  all_goals ring
end Qatlib.Concepts.GradientOracle.DifferenceError
