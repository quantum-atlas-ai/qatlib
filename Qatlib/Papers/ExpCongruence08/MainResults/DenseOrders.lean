/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module

public import Qatlib.Papers.ExpCongruence08.MainResults.SolutionCount

/-!
# Solvability for dense exponent sets

When the two exponent sets have total cardinality greater than the field cardinality, a
translated intersection gives a solution. This is a sufficient condition for the box in
[VanDamShparlinski2008], Corollary 1, in the dense-order regime.

* [van Dam and Shparlinski, 2008](https://arxiv.org/abs/0804.1109v1)
-/

@[expose] public section

set_option autoImplicit false

open Qatlib.Papers.ExpCongruence08.MainResults

namespace Qatlib.Papers.ExpCongruence08.MainResults

/-- Each scaled power occurs at most once in a segment contained in a multiplicative period. -/
private theorem scaled_power_injOn {F : Type*} [Field F] (a f : Fˣ) (r : ℕ)
    (hr : r ≤ orderOf f) :
    Set.InjOn (fun i : ℕ => (a : F) * (f : F) ^ i) (Finset.range r : Set ℕ) := by
  intro i hi j hj hij
  apply pow_injOn_Iio_orderOf (x := f)
    ((Finset.mem_range.mp hi).trans_le hr) ((Finset.mem_range.mp hj).trans_le hr)
  exact Units.ext (by simpa only [Units.val_pow_eq_pow_val] using mul_left_cancel₀ a.ne_zero hij)

/-- If `orderOf f + r > |F|`, the first period meets the translated second segment.
Consequently every nonzero target has a solution when `r ≤ orderOf g`. -/
theorem solvable_of_card_lt_order_add_scan {F : Type*} [Field F] [Fintype F]
    (a b c f g : Fˣ) (r : ℕ) (hr : r ≤ orderOf g)
    (hdense : Fintype.card F < orderOf f + r) :
    ∃ x y : ℕ, x < orderOf f ∧ y < r ∧
      (a : F) * (f : F) ^ x + (b : F) * (g : F) ^ y = (c : F) := by
  classical
  let A := (Finset.range (orderOf f)).image fun x => (a : F) * (f : F) ^ x
  let B := (Finset.range r).image fun y => (c : F) - (b : F) * (g : F) ^ y
  have hA : A.card = orderOf f := by
    rw [Finset.card_image_of_injOn (scaled_power_injOn a f (orderOf f) le_rfl), Finset.card_range]
  have hB : B.card = r := by
    have hinj : Set.InjOn (fun y : ℕ => (c : F) - (b : F) * (g : F) ^ y)
        (Finset.range r : Set ℕ) := by
      intro i hi j hj hij
      exact scaled_power_injOn b g r hr hi hj (sub_right_inj.mp hij)
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  by_contra hnone
  have hdisj : Disjoint A B := by
    refine Finset.disjoint_left.mpr fun z hzA hzB => ?_
    obtain ⟨x, hx, hAx⟩ := Finset.mem_image.mp hzA
    obtain ⟨y, hy, hBy⟩ := Finset.mem_image.mp hzB
    exact hnone ⟨x, y, Finset.mem_range.mp hx, Finset.mem_range.mp hy,
      eq_sub_iff_add_eq.mp (hAx.trans hBy.symm)⟩
  have hcard := Finset.card_le_univ (A ∪ B)
  rw [Finset.card_union_of_disjoint hdisj, hA, hB] at hcard
  exact (not_lt_of_ge hcard) hdense

end Qatlib.Papers.ExpCongruence08.MainResults
