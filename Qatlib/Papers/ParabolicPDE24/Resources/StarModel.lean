/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian

@[expose] public section

/-!
# Star transition model for multidimensional parabolic simulations

Equation (36) of [JinLiu2024] couples one central internal level to one leaf for each spatial
direction. This module models the unit-weight sum of those internal transitions. Its Euclidean
operator norm is `√d`, giving a uniform linear bound for positive `d`. The model concerns the
internal matrix, with Hamiltonian coefficients and quadrature factors outside its scope.

## Main statements

* `starTransition_hermitian`: the star transition matrix is Hermitian.
* `starTransition_norm_eq`: its Euclidean operator norm is `√d`.
* `starTransition_norm_bounds`: for a nonempty star, its Euclidean operator norm lies between
  `√d` and `d`.
* `starTransition_norm_le_uniform`: there is a uniform constant `C > 0`, chosen before `d`, for
  which the Euclidean operator norm is at most `C * d`.
* `starTransition_resource_count`: the internal index has `d + 1` levels and the transition
  matrix has exactly `2 * d` nonzero entries.

## References

* [Jin and Liu, 2024][JinLiu2024]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.ParabolicPDE24.Resources

/-- The real transition matrix of the star qudit: the unique center level is coupled to each of
the `d` leaf levels, with no leaf-to-leaf transitions. -/
def starTransition (d : ℕ) : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ :=
  Matrix.of fun i j =>
    if (i.isLeft ∧ j.isRight) ∨ (i.isRight ∧ j.isLeft) then (1 : ℝ) else 0

/-- The star transition matrix is symmetric, hence Hermitian as a real matrix. -/
theorem starTransition_hermitian (d : ℕ) : (starTransition d).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  cases i <;> cases j <;> simp [starTransition]

/-- The number of nonzero entries in the star transition matrix is twice the number of
center-to-leaf couplings. -/
theorem starTransition_nonzero_count (d : ℕ) :
    ∑ i, ∑ j, (if starTransition d i j ≠ 0 then (1 : ℕ) else 0) = 2 * d := by
  simp only [Fintype.sum_sum_type, starTransition, Matrix.of_apply]
  simp [Fintype.card_fin, Finset.sum_const, Finset.univ_unique]
  omega

/-- The star internal basis has one center plus `d` leaves, and the displayed star matrix has
exactly `2 * d` nonzero entries (both orientations of each of the `d` couplings). -/
theorem starTransition_resource_count (d : ℕ) :
    Fintype.card (Fin 1 ⊕ Fin d) = d + 1 ∧
      ∑ i, ∑ j, (if starTransition d i j ≠ 0 then (1 : ℕ) else 0) = 2 * d :=
  ⟨by simp; omega, starTransition_nonzero_count d⟩

/-- The star matrix represented as a continuous linear map on Euclidean space. -/
private def starTransitionCLM (d : ℕ) :
    EuclideanSpace ℝ (Fin 1 ⊕ Fin d) →L[ℝ] EuclideanSpace ℝ (Fin 1 ⊕ Fin d) :=
  Matrix.toEuclideanCLM (n := Fin 1 ⊕ Fin d) (𝕜 := ℝ) (starTransition d)

/-- The center coordinate of the star map is the sum of all leaf coordinates. -/
private theorem starTransition_center_apply (d : ℕ)
    (x : EuclideanSpace ℝ (Fin 1 ⊕ Fin d)) :
    starTransitionCLM d x (Sum.inl 0) =
      ∑ i, x (Sum.inr i) := by
  rw [starTransitionCLM, Matrix.ofLp_toEuclideanCLM]
  simp [starTransition, Matrix.mulVec,
    dotProduct, Fintype.sum_sum_type]

/-- Every leaf coordinate of the star map is a copy of the center coordinate. -/
private theorem starTransition_leaf_apply (d : ℕ)
    (x : EuclideanSpace ℝ (Fin 1 ⊕ Fin d)) (i : Fin d) :
    starTransitionCLM d x (Sum.inr i) =
      x (Sum.inl 0) := by
  rw [starTransitionCLM, Matrix.ofLp_toEuclideanCLM]
  simp [starTransition, Matrix.mulVec,
    dotProduct, Fintype.sum_sum_type]

/-- The Euclidean operator norm of the `d`-leaf star is `√d`, attained on the center vector. -/
theorem starTransition_norm_eq (d : ℕ) :
    ‖starTransition d‖ = Real.sqrt d := by
  have hmap : ‖starTransition d‖ = ‖starTransitionCLM d‖ := by
    simpa only [starTransitionCLM] using
      (Matrix.l2_opNorm_toEuclideanCLM (starTransition d)).symm
  rw [hmap]
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
    have hleft : ‖starTransitionCLM d x‖ ^ 2 =
        (∑ i, x (Sum.inr i)) ^ 2 + ∑ _i : Fin d, x (Sum.inl 0) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type]
      simp [starTransition_center_apply, starTransition_leaf_apply]
    have hright : ‖x‖ ^ 2 = x (Sum.inl 0) ^ 2 + ∑ i, x (Sum.inr i) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type]
      simp
    have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
      (f := fun i => x (Sum.inr i))
    simp only [Finset.card_univ, Fintype.card_fin] at hcs
    refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
    rw [hleft, mul_pow, Real.sq_sqrt (by positivity), hright, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_add]
    simpa only [add_comm] using add_le_add_right hcs ((d : ℝ) * x (Sum.inl 0) ^ 2)
  · let x : EuclideanSpace ℝ (Fin 1 ⊕ Fin d) :=
      EuclideanSpace.single (Sum.inl 0) (1 : ℝ)
    have hxnorm : ‖x‖ = 1 := by
      simp [x]
    have hout : ‖starTransitionCLM d x‖ = Real.sqrt d := by
      rw [← Real.sqrt_sq (norm_nonneg _), EuclideanSpace.real_norm_sq_eq,
        Fintype.sum_sum_type]
      simp [starTransition_center_apply,
        starTransition_leaf_apply, x]
    simpa only [hout, hxnorm, div_one] using (starTransitionCLM d).ratio_le_opNorm x

/-- For a nonempty `d`-leaf star, the Euclidean operator norm lies between `√d` and `d`. -/
theorem starTransition_norm_bounds {d : ℕ} (hd : 0 < d) :
    Real.sqrt d ≤ ‖starTransition d‖ ∧ ‖starTransition d‖ ≤ (d : ℝ) := by
  rw [starTransition_norm_eq]
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  refine ⟨le_rfl, (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp ?_⟩
  rw [Real.sq_sqrt (by positivity), pow_two]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hd1 (Nat.cast_nonneg d)

/-- There is a single positive constant, fixed before the dimension, that bounds every
nonempty star transition matrix linearly in the Euclidean operator norm.  The constant is `1`;
the sharper exact theorem above gives `√d`. -/
theorem starTransition_norm_le_uniform :
    ∃ C > (0 : ℝ), ∀ d : ℕ, 0 < d → ‖starTransition d‖ ≤ C * (d : ℝ) := by
  refine ⟨1, one_pos, fun d hd => ?_⟩
  simpa using (starTransition_norm_bounds hd).2

end Qatlib.Papers.ParabolicPDE24.Resources
