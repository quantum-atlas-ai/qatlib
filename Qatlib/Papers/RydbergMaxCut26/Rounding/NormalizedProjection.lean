/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.QubitPhysics.GroundBounds
import Qatlib.Papers.RydbergMaxCut26.MomentSdp.GramFactor

/-!
# Normalization of projected Bloch vectors

The map `normalize` divides a three-dimensional coordinate vector by the square root of its
squared norm. Its value at zero has squared norm zero, so `roundVector` always lies in the Bloch
ball and defines a positive semidefinite, trace-one product state for every projection matrix.
See [CrostaSaubanereHuber2026].

## Main statements

* `normalize_sqnorm`: distinguishes the zero and unit squared-norm cases.
* `rounded_product_density`: proves physicality of the rounded product state.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Matrix
open Qatlib
open Qatlib.Foundations.PureStateMath
open scoped Classical ComplexOrder
namespace Qatlib.Papers.RydbergMaxCut26.Rounding.Projection
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Bloch Qatlib.Papers.RydbergMaxCut26.MomentSdp.Gram

/-- The coordinate vector obtained by dividing each entry by the square root of its squared
norm. -/
noncomputable def normalize (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun a => v a/Real.sqrt (sqnorm v)

/-- The squared norm of a normalized vector is zero when the original squared norm is zero, and
one otherwise. -/
theorem normalize_sqnorm (v : Fin 3 → ℝ) :
    sqnorm (normalize v) = if sqnorm v=0 then 0 else 1 := by
  have hs : 0 ≤ sqnorm v := Finset.sum_nonneg (fun a _ => sq_nonneg (v a))
  have he : sqnorm (normalize v) = sqnorm v/(Real.sqrt (sqnorm v))^2 := by
    simp only [sqnorm,normalize,div_pow,Finset.sum_div]
  rw [he,Real.sq_sqrt hs]
  by_cases hz : sqnorm v=0
  · simp only [hz,div_zero,ite_true]
  · simp only [hz,ite_false,div_self hz]

/-- Every normalized coordinate vector has squared norm at most one. -/
theorem normalize_ball (v : Fin 3 → ℝ) : sqnorm (normalize v)≤1 := by
  rw [normalize_sqnorm]
  split <;> norm_num

/-- The normalized three-dimensional projection of the Gram fit vector at a site under the
matrix `R`. -/
noncomputable def roundVector {n : ℕ} (Δ : Matrix (MomentIndex n) (MomentIndex n) ℝ)
    (hΔ : Δ.PosSemidef) (R : Fin 3 → (Fin 2×MomentIndex n) → ℝ) (i : Fin n) : Fin 3 → ℝ :=
  normalize (fun a => ∑ c, R a c*fitVector Δ hΔ i c)

/-- For any positive semidefinite moment matrix and any projection matrix, the product state
built from `roundVector` is positive semidefinite and has trace one. -/
theorem rounded_product_density {n : ℕ} (Δ : Matrix (MomentIndex n) (MomentIndex n) ℝ)
    (hΔ : Δ.PosSemidef) (R : Fin 3 → (Fin 2×MomentIndex n) → ℝ) :
    (productState (roundVector Δ hΔ R)).PosSemidef ∧ (productState (roundVector Δ hΔ R)).trace=1 :=
  product_density _ (fun _ => normalize_ball _)
end Qatlib.Papers.RydbergMaxCut26.Rounding.Projection
