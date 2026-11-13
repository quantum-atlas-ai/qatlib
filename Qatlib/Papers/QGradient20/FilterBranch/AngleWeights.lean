/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QGradient20.FilterBranch.ActualVector

/-!
# Trigonometric weights of the successful branch

For nonzero cosine, the substitution `ξ = tan² η` converts the successful-vector weights into
`cos² η` and `sin² η`. `actual_source_angle_vector` gives the resulting exact vector identity
for either update sign. The mathematical context is [GaoEtAl2021].

## Main statements

* `source_sin_weight`: If `cos η` is nonzero, `tan² η / (1 + tan² η)` equals `sin² η`.
* `actual_source_angle_vector`: If `cos η` is nonzero, the successful vector at parameter `tan²
  η` is the input weighted by `cos² η` plus the signed projected derivative action weighted by
  `sin² η`.

## References

* [Gao et al., 2021][GaoEtAl2021]
-/

set_option autoImplicit false
noncomputable section
open scoped Matrix.Norms.L2Operator
namespace Qatlib.Papers.QGradient20.FilterBranch
variable {I : Type} [Fintype I] [DecidableEq I]

/-- If `cos η` is nonzero, the reciprocal of `1 + tan² η` equals `cos² η`. -/
theorem source_cos_weight (η : ℝ) (hc : Real.cos η ≠ 0) :
    (1+Real.tan η^2)⁻¹=Real.cos η^2 := by
  have ht : Real.tan η^2=Real.sin η^2/Real.cos η^2 := by rw [Real.tan_eq_sin_div_cos,div_pow]
  rw [ht]
  have hd : 1+Real.sin η^2/Real.cos η^2=(Real.cos η^2)⁻¹ := by
    field_simp [hc]
    nlinarith [Real.sin_sq_add_cos_sq η]
  rw [hd,inv_inv]

/-- If `cos η` is nonzero, `tan² η / (1 + tan² η)` equals `sin² η`. -/
theorem source_sin_weight (η : ℝ) (hc : Real.cos η ≠ 0) :
    (1+Real.tan η^2)⁻¹*Real.tan η^2=Real.sin η^2 := by
  rw [source_cos_weight η hc,Real.tan_eq_sin_div_cos,div_pow]
  field_simp

/-- If `cos η` is nonzero, the successful vector at parameter `tan² η` is the input weighted by
`cos² η` plus the signed projected derivative action weighted by `sin² η`. See
[GaoEtAl2021]. -/
theorem actual_source_angle_vector (zero : I) (M : Matrix I I ℂ) (η : ℝ) (hc : Real.cos η≠0)
    (ascent : Bool) (x : EuclideanSpace ℂ I) :
    successfulVector zero M (Real.tan η^2) ascent x=
      (Real.cos η^2:ℝ) • x + (branchSign ascent*Real.sin η^2:ℝ) • project zero (derivativeAction M x) := by
  rw [successfulVector,update,smul_add,smul_smul,source_cos_weight η hc]
  have h : Real.cos η^2*(branchSign ascent*Real.tan η^2)=branchSign ascent*Real.sin η^2 := by
    have he := source_sin_weight η hc
    rw [source_cos_weight η hc] at he
    calc
      Real.cos η^2*(branchSign ascent*Real.tan η^2)=branchSign ascent*(Real.cos η^2*Real.tan η^2) := by ring
      _ = _ := by rw [he]
  rw [h]

end Qatlib.Papers.QGradient20.FilterBranch
