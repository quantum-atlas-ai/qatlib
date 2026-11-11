/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianMatrix
import Mathlib.Tactic

/-!
# Orthogonal residuals of unit input vectors

The direction `residualDirection u v` normalizes the component of `v` orthogonal to `u`. When
both inputs are unit and their inner product has absolute value less than one, this gives an
orthonormal pair and reconstructs the second Gaussian projection through `correlated`. See
[CrostaSaubanereHuber2026].

## Main statements

* `residual_geometry`: gives unit norm, orthogonality, and the decomposition of `v`.
* `project_reconstruction`: expresses the second projection as a correlated combination.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory
open Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianPair
open Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianMatrix

namespace Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianJoint

/-- The vector `(v - ⟪u, v⟫ • u) / √(1 - ⟪u, v⟫²)`, written using scalar multiplication. -/
def residualDirection {I : Type} [Fintype I] (u v : Row I) : Row I :=
  (Real.sqrt (1-(inner ℝ u v)^2))⁻¹ • (v-(inner ℝ u v) • u)

/-- The residual scale `√(1 - ⟪u, v⟫²)` is positive when the input inner product has absolute
value less than one. -/
theorem residual_scale_pos {I : Type} [Fintype I] (u v : Row I) (ht : |inner ℝ u v|<1) :
    0<Real.sqrt (1-(inner ℝ u v)^2) := by
  apply Real.sqrt_pos.mpr
  have h := abs_lt.mp ht
  nlinarith

/-- For unit inputs with inner product of absolute value less than one, the residual direction
is unit and orthogonal to `u`, and reconstructs `v` with coefficients `⟪u, v⟫` and `√(1 -
⟪u, v⟫²)`. -/
theorem residual_geometry {I : Type} [Fintype I] (u v : Row I)
    (hu : ‖u‖=1) (hv : ‖v‖=1) (ht : |inner ℝ u v|<1) :
    ‖residualDirection u v‖=1 ∧ inner ℝ u (residualDirection u v)=0 ∧
      v=(inner ℝ u v) • u+Real.sqrt (1-(inner ℝ u v)^2) • residualDirection u v := by
  let t := inner ℝ u v
  let s := Real.sqrt (1-t^2)
  have hs : 0<s := residual_scale_pos u v ht
  have huu : inner ℝ u u=1 := by rw [real_inner_self_eq_norm_sq,hu];norm_num
  have hvv : inner ℝ v v=1 := by rw [real_inner_self_eq_norm_sq,hv];norm_num
  have hvu : inner ℝ v u=t := (real_inner_comm v u).symm
  have horth : inner ℝ u (v-t • u)=0 := by
    rw [inner_sub_right,inner_smul_right,huu]
    dsimp [t]
    ring
  have hsq : ‖v-t • u‖^2=1-t^2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,inner_smul_right,huu,hvv,hvu]
    dsimp [t]
    ring
  have hnorm : ‖v-t • u‖=s := by
    calc
      _ = Real.sqrt (‖v-t • u‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ = _ := by rw [hsq]
  constructor
  · change ‖s⁻¹ • (v-t • u)‖=1
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs),hnorm,inv_mul_cancel₀ hs.ne']
  constructor
  · change inner ℝ u (s⁻¹ • (v-t • u))=0
    rw [inner_smul_right,horth,mul_zero]
  · change v=t • u+s • (s⁻¹ • (v-t • u))
    rw [smul_smul,mul_inv_cancel₀ hs.ne',one_smul]
    module

/-- For unit inputs with inner product of absolute value less than one, projecting `v` equals
the correlated combination of the projections of `u` and its residual direction. -/
theorem project_reconstruction {I : Type} [Fintype I] (u v : Row I)
    (hu : ‖u‖=1) (hv : ‖v‖=1) (ht : |inner ℝ u v|<1) (R : Rows I) :
    project v R=correlated (inner ℝ u v) (project u R,project (residualDirection u v) R) := by
  have h := (residual_geometry u v hu hv ht).2.2
  ext r
  change inner ℝ v (R r)=inner ℝ u v*inner ℝ u (R r)+
    Real.sqrt (1-(inner ℝ u v)^2)*inner ℝ (residualDirection u v) (R r)
  conv_lhs => rw [h]
  simp only [inner_add_left,real_inner_smul_left]

end Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianJoint
