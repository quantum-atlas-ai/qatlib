/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BinaryOptEncode.ExactGadgets.LocalGadgets

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.BinaryOptEncode.ExactGadgets
open scoped BigOperators

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

def squaredResidual {S J : Type*} [Fintype J] (r : J → S → ℤ) (x : S) : ℝ :=
  ∑ j, (r j x : ℝ) ^ 2

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

def safePenalty {S : Type*} [Fintype S] (f : S → ℝ) : ℝ :=
  2 * (∑ x, |f x|) + 1

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
