/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BinaryOptEncode.ExactGadgets.LocalGadgets

/-!
# Exact penalties for finite optimization

This module proves that a penalty exceeding the objective range divided by a residual gap
separates infeasible points from feasible ones and preserves constrained minimizers. For
finitely many integer residuals, `squaredResidual` has gap at least one away from zero, and
`safePenalty` supplies an explicit coefficient on a finite search space. These results support
exact optimization encodings in the setting of [SongEtAl2023].

## Main statements

* `penalty_argmin_iff`: unconstrained minimizers of the penalized objective are exactly the
  feasible constrained minimizers under the separation hypotheses.
* `squaredResidual_zero_iff`: the squared residual vanishes exactly when all integer constraints
  vanish.
* `safePenalty_argmin_iff`: the explicit coefficient `safePenalty` yields the minimizer
  equivalence whenever a feasible point exists.

## References

* [Song et al., 2023][SongEtAl2023]
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.BinaryOptEncode.ExactGadgets
open scoped BigOperators

/-- If the positive penalty times the residual gap exceeds the objective range, every point with
nonzero residual has strictly larger penalized objective than any feasible point. -/
theorem penalty_infeasible_separation {S : Type*} (f residual : S → ℝ)
    (lower upper penalty gap : ℝ) (hpen : 0 < penalty)
    (hsize : upper - lower < penalty * gap)
    (hbounds : ∀ x, lower ≤ f x ∧ f x ≤ upper)
    (hgap : ∀ x, residual x ≠ 0 → gap ≤ residual x)
    (x feasible : S) (hx : residual x ≠ 0) (hf : residual feasible = 0) :
    f feasible + penalty * residual feasible < f x + penalty * residual x := by
  have hp := mul_le_mul_of_nonneg_left (hgap x hx) hpen.le
  rw [hf, mul_zero, add_zero]
  linarith [(hbounds x).1, (hbounds feasible).2]

/-- Given a feasible point and a positive penalty whose residual-gap contribution exceeds the
objective range, global minimizers of the penalized objective are exactly the feasible
minimizers of the original objective. -/
theorem penalty_argmin_iff {S : Type*} (f residual : S → ℝ)
    (lower upper penalty gap : ℝ) (hpen : 0 < penalty)
    (hsize : upper - lower < penalty * gap)
    (hbounds : ∀ x, lower ≤ f x ∧ f x ≤ upper)
    (hgap : ∀ x, residual x ≠ 0 → gap ≤ residual x)
    (feasible : S) (hf : residual feasible = 0) (x : S) :
    (∀ y, f x + penalty * residual x ≤ f y + penalty * residual y) ↔
      residual x = 0 ∧ ∀ y, residual y = 0 → f x ≤ f y := by
  constructor
  · intro hmin
    have hx : residual x = 0 := by
      by_contra hx
      exact (not_lt_of_ge (hmin feasible))
        (penalty_infeasible_separation f residual lower upper penalty gap hpen hsize
          hbounds hgap x feasible hx hf)
    refine ⟨hx, ?_⟩
    intro y hy
    simpa [hx, hy] using hmin y
  · rintro ⟨hx, hmin⟩ y
    by_cases hy : residual y = 0
    · simpa [hx, hy] using hmin y hy
    · exact (penalty_infeasible_separation f residual lower upper penalty gap hpen hsize
        hbounds hgap y x hy hx).le

/-- The sum of squares of a finite family of integer constraint residuals, regarded as a real
number. -/
def squaredResidual {S J : Type*} [Fintype J] (r : J → S → ℤ) (x : S) : ℝ :=
  ∑ j, (r j x : ℝ) ^ 2

/-- The sum of squared integer residuals is zero exactly when every residual is zero. -/
theorem squaredResidual_zero_iff {S J : Type*} [Fintype J] (r : J → S → ℤ) (x : S) :
    squaredResidual r x = 0 ↔ ∀ j, r j x = 0 := by
  classical
  constructor
  · intro h j
    have hj : (r j x : ℝ) ^ 2 ≤ squaredResidual r x :=
      Finset.single_le_sum (fun k _ => sq_nonneg (r k x : ℝ)) (Finset.mem_univ j)
    have hz : (r j x : ℝ) = 0 := by nlinarith [sq_nonneg (r j x : ℝ)]
    exact_mod_cast hz
  · intro h
    simp [squaredResidual, h]

/-- A nonzero sum of squared integer residuals is at least one. -/
theorem squaredResidual_gap {S J : Type*} [Fintype J] (r : J → S → ℤ) (x : S)
    (hne : squaredResidual r x ≠ 0) : 1 ≤ squaredResidual r x := by
  classical
  have hex : ∃ j, r j x ≠ 0 := by
    by_contra! h
    exact hne ((squaredResidual_zero_iff r x).mpr h)
  obtain ⟨j, hj⟩ := hex
  have hs : (1 : ℤ) ≤ (r j x) ^ 2 := by
    have hp := sq_pos_of_ne_zero hj
    omega
  have hs' : (1 : ℝ) ≤ (r j x : ℝ) ^ 2 := by exact_mod_cast hs
  exact hs'.trans
    (Finset.single_le_sum (fun k _ => sq_nonneg (r k x : ℝ)) (Finset.mem_univ j))

/-- The explicit penalty coefficient twice the sum of absolute objective values over the finite
search space, plus one. -/
def safePenalty {S : Type*} [Fintype S] (f : S → ℝ) : ℝ :=
  2 * (∑ x, |f x|) + 1

/-- On a finite search space with a feasible point, adding `safePenalty` times the squared
integer residual sum makes the global minimizers exactly the feasible minimizers of the
original objective. -/
theorem safePenalty_argmin_iff {S J : Type*} [Fintype S] [Fintype J]
    (f : S → ℝ) (r : J → S → ℤ) (feasible : S) (hf : ∀ j, r j feasible = 0) (x : S) :
    (∀ y, f x + safePenalty f * squaredResidual r x ≤
      f y + safePenalty f * squaredResidual r y) ↔
      (∀ j, r j x = 0) ∧ ∀ y, (∀ j, r j y = 0) → f x ≤ f y := by
  classical
  let A : ℝ := ∑ y, |f y|
  have hA : 0 ≤ A := Finset.sum_nonneg fun y _ => abs_nonneg (f y)
  have hb : ∀ y, -A ≤ f y ∧ f y ≤ A := by
    intro y
    have hy : |f y| ≤ A :=
      Finset.single_le_sum (fun z _ => abs_nonneg (f z)) (Finset.mem_univ y)
    exact abs_le.mp hy
  have hpenPos : 0 < safePenalty f := by
    change 0 < 2 * A + 1
    linarith
  have hsize : A - (-A) < safePenalty f * 1 := by
    change A - (-A) < (2 * A + 1) * 1
    linarith
  have he := penalty_argmin_iff f (squaredResidual r) (-A) A (safePenalty f) 1
    hpenPos hsize hb (fun y hy => squaredResidual_gap r y hy) feasible
    ((squaredResidual_zero_iff r feasible).mpr hf) x
  simpa only [squaredResidual_zero_iff] using he

end Qatlib.Concepts.BinaryOptEncode.ExactGadgets
