/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Data.Fintype.Units

/-!
# Counting solutions of exponential congruences

The functions `numSolutions` and `numSolutionsAt` count exponent pairs in finite boxes
satisfying `a * f ^ x + b * g ^ y = c`. Elementary counting identities give size bounds and
existence criteria, while assumed deviation and second-moment estimates yield conditional
worst-case and typical solvability statements. These statements formalize components of
[VanDamShparlinski2008].

## Main statements

* `sum_numSolutionsAt`: counts all exponent pairs by summing over target field elements.
* `lemma2_typical_count_of_second_moment`: bounds an exceptional set using a supplied
  second-moment estimate.
* `corollary1_solvable_of_bound`: deduces solvability from a supplied uniform counting estimate.

## References

* [van Dam and Shparlinski, 2008][VanDamShparlinski2008]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ExpCongruence08.MainResults

open scoped Classical

/-- The field value `a * f ^ x + b * g ^ y` associated with an exponent pair. -/
def solValue {F : Type*} [Field F] (a b f g : Fˣ) (p : ℕ × ℕ) : F :=
  (a : F) * (f : F) ^ p.1 + (b : F) * (g : F) ^ p.2

/-- The number of exponent pairs with `x < s` and `y < r` whose field value equals the nonzero
target `c`. See [VanDamShparlinski2008]. -/
def numSolutions {F : Type*} [Field F] (a b c f g : Fˣ) (s r : ℕ) : ℕ :=
  (((Finset.range s).product (Finset.range r)).filter
    (fun p : ℕ × ℕ => solValue a b f g p = (c : F))).card

/-- The number of exponent pairs in the box with field value equal to the arbitrary target `c`. -/
def numSolutionsAt {F : Type*} [Field F] (a b : Fˣ) (c : F) (f g : Fˣ) (s r : ℕ) : ℕ :=
  (((Finset.range s).product (Finset.range r)).filter
    (fun p : ℕ × ℕ => solValue a b f g p = c)).card

/-- Counting solutions for a unit target agrees with counting for its underlying field element.
See [VanDamShparlinski2008]. -/
theorem numSolutions_eq_numSolutionsAt {F : Type*} [Field F]
    (a b c f g : Fˣ) (s r : ℕ) :
    numSolutions a b c f g s r = numSolutionsAt a b (c : F) f g s r := rfl

/-- The box solution count is zero exactly when every exponent pair in that box fails the
equation. See [VanDamShparlinski2008]. -/
theorem numSolutions_eq_zero_iff {F : Type*} [Field F] (a b c f g : Fˣ) (s r : ℕ) :
    numSolutions a b c f g s r = 0 ↔
      ∀ x y : ℕ, x < s → y < r →
        (a : F) * (f : F) ^ x + (b : F) * (g : F) ^ y ≠ (c : F) := by
  classical
  unfold numSolutions solValue
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h x y hx hy
    exact h (Finset.mk_mem_product (Finset.mem_range.mpr hx) (Finset.mem_range.mpr hy))
  · intro h p hp
    exact fun heq =>
      h p.1 p.2 (Finset.mem_range.mp (Finset.mem_product.mp hp).1)
        (Finset.mem_range.mp (Finset.mem_product.mp hp).2) heq

/-- A positive box solution count yields exponents satisfying the equation within the box. -/
theorem exists_of_numSolutions_pos {F : Type*} [Field F] (a b c f g : Fˣ) (s r : ℕ)
    (h : 0 < numSolutions a b c f g s r) :
    ∃ x y : ℕ, x < s ∧ y < r ∧
      (a : F) * (f : F) ^ x + (b : F) * (g : F) ^ y = (c : F) := by
  classical
  unfold numSolutions solValue at h
  rw [Finset.card_pos] at h
  obtain ⟨p, hp⟩ := h
  rw [Finset.mem_filter] at hp
  exact ⟨p.1, p.2, Finset.mem_range.mp (Finset.mem_product.mp hp.1).1,
    Finset.mem_range.mp (Finset.mem_product.mp hp.1).2, hp.2⟩

/-- The multiplicative order of a unit in a finite field is at most the field cardinality minus
one. -/
theorem orderOf_le_card_sub_one {F : Type*} [Field F] [Fintype F] (f : Fˣ) :
    orderOf f ≤ Fintype.card F - 1 := by
  classical
  have hdvd := orderOf_dvd_card (x := f)
  rw [Fintype.card_units] at hdvd
  have hq : 0 < Fintype.card F - 1 := by
    have := Fintype.one_lt_card (α := F)
    omega
  exact Nat.le_of_dvd hq hdvd

/-- If both box side lengths are within the respective multiplicative orders, the solution count
is at most the second side length. See [VanDamShparlinski2008]. -/
theorem numSolutions_le_r {F : Type*} [Field F] (a b c f g : Fˣ) (s r : ℕ)
    (hs : s ≤ orderOf f) (hr : r ≤ orderOf g) :
    numSolutions a b c f g s r ≤ r := by
  classical
  unfold numSolutions solValue
  have key : (((Finset.range s).product (Finset.range r)).filter
      (fun p : ℕ × ℕ => (a : F) * (f : F) ^ p.1 + (b : F) * (g : F) ^ p.2 = (c : F))).card
      ≤ (Finset.range r).card := by
    refine Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.2) ?_ ?_
    · intro p hp
      exact Finset.mem_range.mpr
        (Finset.mem_range.mp (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2)
    · rintro ⟨x, y⟩ hp ⟨x', y'⟩ hq heq
      simp only at heq
      have hpbox := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      have hqbox := Finset.mem_product.mp (Finset.mem_filter.mp hq).1
      have hpeq : (a : F) * (f : F) ^ x + (b : F) * (g : F) ^ y = (c : F) :=
        (Finset.mem_filter.mp hp).2
      have hqeq : (a : F) * (f : F) ^ x' + (b : F) * (g : F) ^ y' = (c : F) :=
        (Finset.mem_filter.mp hq).2
      have hx : x < orderOf f := lt_of_lt_of_le (Finset.mem_range.mp hpbox.1) hs
      have hx' : x' < orderOf f := lt_of_lt_of_le (Finset.mem_range.mp hqbox.1) hs
      have hval : ((f : Fˣ) ^ x) = ((f : Fˣ) ^ x') := by
        apply Units.ext
        have hsum : (a : F) * (f : F) ^ x + (b : F) * (g : F) ^ y'
            = (a : F) * (f : F) ^ x' + (b : F) * (g : F) ^ y' := by
          have h := hpeq.trans hqeq.symm
          rwa [heq] at h
        exact mul_left_cancel₀ (Units.ne_zero a) (add_right_cancel hsum)
      have hxeq : x = x' := pow_injOn_Iio_orderOf (x := f) hx hx' hval
      exact Prod.ext hxeq heq
  simpa using key

/-- If both box side lengths are within the respective multiplicative orders, the solution count
is at most the first side length. See [VanDamShparlinski2008]. -/
theorem numSolutions_le_s {F : Type*} [Field F] (a b c f g : Fˣ) (s r : ℕ)
    (hs : s ≤ orderOf f) (hr : r ≤ orderOf g) :
    numSolutions a b c f g s r ≤ s := by
  classical
  unfold numSolutions solValue
  have key : (((Finset.range s).product (Finset.range r)).filter
      (fun p : ℕ × ℕ => (a : F) * (f : F) ^ p.1 + (b : F) * (g : F) ^ p.2 = (c : F))).card
      ≤ (Finset.range s).card := by
    refine Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.1) ?_ ?_
    · intro p hp
      exact Finset.mem_range.mpr
        (Finset.mem_range.mp (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1)
    · rintro ⟨x, y⟩ hp ⟨x', y'⟩ hq heq
      simp only at heq
      have hpbox := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      have hqbox := Finset.mem_product.mp (Finset.mem_filter.mp hq).1
      have hpeq : (a : F) * (f : F) ^ x + (b : F) * (g : F) ^ y = (c : F) :=
        (Finset.mem_filter.mp hp).2
      have hqeq : (a : F) * (f : F) ^ x' + (b : F) * (g : F) ^ y' = (c : F) :=
        (Finset.mem_filter.mp hq).2
      have hy : y < orderOf g := lt_of_lt_of_le (Finset.mem_range.mp hpbox.2) hr
      have hy' : y' < orderOf g := lt_of_lt_of_le (Finset.mem_range.mp hqbox.2) hr
      have hval : ((g : Fˣ) ^ y) = ((g : Fˣ) ^ y') := by
        apply Units.ext
        have hsum : (a : F) * (f : F) ^ x + (b : F) * (g : F) ^ y
            = (a : F) * (f : F) ^ x + (b : F) * (g : F) ^ y' := by
          have h := hpeq.trans hqeq.symm
          rwa [← heq] at h
        exact mul_left_cancel₀ (Units.ne_zero b) (add_left_cancel hsum)
      have hyeq : y = y' := pow_injOn_Iio_orderOf (x := g) hy hy' hval
      exact Prod.ext heq hyeq
  simpa using key

/-- Increasing the second side length cannot decrease the solution count. -/
theorem numSolutions_mono_r {F : Type*} [Field F] (a b c f g : Fˣ) (s : ℕ)
    {r₁ r₂ : ℕ} (h : r₁ ≤ r₂) :
    numSolutions a b c f g s r₁ ≤ numSolutions a b c f g s r₂ := by
  classical
  unfold numSolutions solValue
  apply Finset.card_le_card
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  refine ⟨Finset.mem_product.mpr ?_, hp.2⟩
  exact ⟨(Finset.mem_product.mp hp.1).1,
    Finset.mem_range.mpr (lt_of_lt_of_le
      (Finset.mem_range.mp (Finset.mem_product.mp hp.1).2) h)⟩

/-- When the second side covers the order of `g`, positivity of the count with first side
`orderOf f` is equivalent to unrestricted solvability. -/
theorem numSolutions_pos_iff_exists {F : Type*} [Field F] [Fintype F] (a b c f g : Fˣ) (r : ℕ)
    (hr : orderOf g ≤ r) :
    0 < numSolutions a b c f g (orderOf f) r ↔
      ∃ x y : ℕ, (a : F) * (f : F) ^ x + (b : F) * (g : F) ^ y = (c : F) := by
  constructor
  · intro h
    obtain ⟨x, y, _hx, _hy, hxy⟩ := exists_of_numSolutions_pos a b c f g (orderOf f) r h
    exact ⟨x, y, hxy⟩
  · rintro ⟨x, y, hxy⟩
    classical
    have hx : x % orderOf f < orderOf f := Nat.mod_lt _ (orderOf_pos f)
    have hy : y % orderOf g < r :=
      lt_of_lt_of_le (Nat.mod_lt _ (orderOf_pos g)) hr
    have hx' : (f : F) ^ (x % orderOf f) = (f : F) ^ x := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, pow_mod_orderOf]
    have hy' : (g : F) ^ (y % orderOf g) = (g : F) ^ y := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, pow_mod_orderOf]
    have hmem : (x % orderOf f, y % orderOf g) ∈
        ((Finset.range (orderOf f)).product (Finset.range r)).filter
          (fun p : ℕ × ℕ => solValue a b f g p = (c : F)) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ?_, ?_⟩
      · exact ⟨Finset.mem_range.mpr hx, Finset.mem_range.mpr hy⟩
      · show solValue a b f g (x % orderOf f, y % orderOf g) = (c : F)
        show (a : F) * (f : F) ^ (x % orderOf f) + (b : F) * (g : F) ^ (y % orderOf g) = (c : F)
        rw [hx', hy']; exact hxy
    exact Finset.card_pos.mpr ⟨_, hmem⟩

/-- Summing the box solution counts over all field targets counts each of the `s * r` exponent
pairs once. See [VanDamShparlinski2008]. -/
theorem sum_numSolutionsAt {F : Type*} [Field F] [Fintype F] (a b f g : Fˣ) (s r : ℕ) :
    (∑ c : F, numSolutionsAt a b c f g s r) = s * r := by
  classical
  unfold numSolutionsAt
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.range s).product (Finset.range r))
    (t := (Finset.univ : Finset F)) (f := fun p => solValue a b f g p)
    (fun p _ => Finset.mem_univ _)
  simpa using h.symm

/-- Some field target has box solution count at least the average `s * r / |F|`. -/
theorem exists_numSolutionsAt_ge {F : Type*} [Field F] [Fintype F]
    (a b f g : Fˣ) (s r : ℕ) :
    ∃ c : F, (s : ℝ) * (r : ℝ) / (Fintype.card F : ℝ)
      ≤ (numSolutionsAt a b c f g s r : ℝ) := by
  classical
  haveI : Nonempty F := ⟨0⟩
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  by_contra h
  push_neg at h
  have hsum_lt : (∑ c : F, (numSolutionsAt a b c f g s r : ℝ))
      < ∑ _c : F, ((s : ℝ) * (r : ℝ) / (Fintype.card F : ℝ)) := by
    refine Finset.sum_lt_sum (fun c _ => le_of_lt (h c)) ⟨Classical.arbitrary F, Finset.mem_univ _,
      h (Classical.arbitrary F)⟩
  have hsum : (∑ c : F, (numSolutionsAt a b c f g s r : ℝ)) = (s : ℝ) * (r : ℝ) := by
    rw [← Nat.cast_sum, sum_numSolutionsAt (F := F)]
    push_cast
    ring
  have hconst : (∑ _c : F, ((s : ℝ) * (r : ℝ) / (Fintype.card F : ℝ)))
      = (s : ℝ) * (r : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  rw [hsum, hconst] at hsum_lt
  exact lt_irrefl _ hsum_lt

/-- For `r ≤ orderOf g`, the deviation of the count from `r * orderOf f / (|F| - 1)` is at most
`orderOf g`. See [VanDamShparlinski2008]. -/
theorem abs_numSolutions_sub_le_orderOf {F : Type*} [Field F] [Fintype F]
    (a b c f g : Fˣ) (r : ℕ) (hr : r ≤ orderOf g) :
    |(numSolutions a b c f g (orderOf f) r : ℝ)
        - (r : ℝ) * (orderOf f : ℝ) / ((Fintype.card F : ℝ) - 1)|
      ≤ (orderOf g : ℝ) := by
  classical
  have hNle : (numSolutions a b c f g (orderOf f) r : ℝ) ≤ (r : ℝ) := by
    exact_mod_cast numSolutions_le_r a b c f g (orderOf f) r le_rfl hr
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have hqR : (1 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hq
  have hqsub : (0 : ℝ) < (Fintype.card F : ℝ) - 1 := by linarith
  have hsle : (orderOf f : ℝ) ≤ (Fintype.card F : ℝ) - 1 := by
    have hq1le : 1 ≤ Fintype.card F := le_of_lt hq
    have h := orderOf_le_card_sub_one f
    have h' : ((orderOf f : ℕ) : ℝ) ≤ ((Fintype.card F - 1 : ℕ) : ℝ) := by
      exact_mod_cast h
    rwa [Nat.cast_sub hq1le, Nat.cast_one] at h'
  have hrs : (r : ℝ) * (orderOf f : ℝ) / ((Fintype.card F : ℝ) - 1) ≤ (r : ℝ) := by
    rw [div_le_iff₀ hqsub]
    nlinarith [Nat.cast_nonneg (α := ℝ) r]
  have hrg : (r : ℝ) ≤ (orderOf g : ℝ) := by exact_mod_cast hr
  have hrsnn : (0 : ℝ) ≤ (r : ℝ) * (orderOf f : ℝ) / ((Fintype.card F : ℝ) - 1) := by
    positivity
  rw [abs_le]
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (numSolutions a b c f g (orderOf f) r)]

/-- If `(|F| - 1) ^ 2 / orderOf f < r ≤ orderOf g`, the equation has a solution with `x <
orderOf f` and `y < r`. See [VanDamShparlinski2008]. -/
theorem corollary1_solvable_weak {F : Type*} [Field F] [Fintype F]
    (a b c f g : Fˣ) (r : ℕ)
    (hlow : ((Fintype.card F : ℝ) - 1) ^ 2 / (orderOf f : ℝ) < (r : ℝ))
    (hup : r ≤ orderOf g) :
    ∃ x y : ℕ, x < orderOf f ∧ y < r ∧
      (a : F) * (f : F) ^ x + (b : F) * (g : F) ^ y = (c : F) := by
  classical
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have hqR : (1 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hq
  have hqsub : (0 : ℝ) < (Fintype.card F : ℝ) - 1 := by linarith
  have hspos : (0 : ℝ) < (orderOf f : ℝ) := by
    exact_mod_cast orderOf_pos f
  by_contra hno
  push_neg at hno
  have hzero : numSolutions a b c f g (orderOf f) r = 0 :=
    (numSolutions_eq_zero_iff a b c f g (orderOf f) r).mpr hno
  have hb := abs_numSolutions_sub_le_orderOf a b c f g r hup
  have hcount : (r : ℝ) * (orderOf f : ℝ) / ((Fintype.card F : ℝ) - 1)
      ≤ (orderOf g : ℝ) := by
    rw [hzero, Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg (by positivity)] at hb
    exact hb
  have hrg : (orderOf g : ℝ) ≤ (Fintype.card F : ℝ) - 1 := by
    have hq1le : 1 ≤ Fintype.card F := le_of_lt hq
    have h := orderOf_le_card_sub_one g
    have h' : ((orderOf g : ℕ) : ℝ) ≤ ((Fintype.card F - 1 : ℕ) : ℝ) := by
      exact_mod_cast h
    rwa [Nat.cast_sub hq1le, Nat.cast_one] at h'
  have hmain : (r : ℝ) * (orderOf f : ℝ) / ((Fintype.card F : ℝ) - 1)
      ≤ (Fintype.card F : ℝ) - 1 := le_trans hcount hrg
  rw [div_le_iff₀ hqsub] at hmain

  have hrle : (r : ℝ) ≤ ((Fintype.card F : ℝ) - 1) ^ 2 / (orderOf f : ℝ) := by
    rw [le_div_iff₀ hspos]
    nlinarith [hmain]
  linarith

/-- The finite set of nonzero targets whose count deviates from `r * s / |F|` by at least `δ *
√r`. See [VanDamShparlinski2008]. -/
def badSet {F : Type*} [Field F] [Fintype F] (a b f g : Fˣ) (s r : ℕ) (δ : ℝ) :
    Finset Fˣ :=
  Finset.univ.filter (fun c : Fˣ =>
    δ * Real.sqrt (r : ℝ) ≤
      |(numSolutions a b c f g s r : ℝ)
        - (r : ℝ) * (s : ℝ) / (Fintype.card F : ℝ)|)

/-- For positive `δ`, the exceptional-set cardinality times `δ ^ 2 * r` is bounded by the sum of
squared count deviations. See [VanDamShparlinski2008]. -/
theorem badSet_card_mul_le_sum_sq {F : Type*} [Field F] [Fintype F]
    (a b f g : Fˣ) (s r : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ((badSet a b f g s r δ).card : ℝ) * (δ ^ 2 * (r : ℝ))
      ≤ ∑ c : Fˣ, ((numSolutions a b c f g s r : ℝ)
          - (r : ℝ) * (s : ℝ) / (Fintype.card F : ℝ)) ^ 2 := by
  classical
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hδ2 : (0 : ℝ) ≤ δ ^ 2 := sq_nonneg δ
  have hpt : ∀ c ∈ badSet a b f g s r δ,
      δ ^ 2 * (r : ℝ) ≤ ((numSolutions a b c f g s r : ℝ)
          - (r : ℝ) * (s : ℝ) / (Fintype.card F : ℝ)) ^ 2 := by
    intro c hc
    simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    have hlow : -( |(numSolutions a b c f g s r : ℝ)
          - (r : ℝ) * (s : ℝ) / (Fintype.card F : ℝ)| ) ≤ δ * Real.sqrt (r : ℝ) := by
      have hpos : (0 : ℝ) ≤ δ * Real.sqrt (r : ℝ) := by positivity
      linarith [abs_nonneg ((numSolutions a b c f g s r : ℝ)
          - (r : ℝ) * (s : ℝ) / (Fintype.card F : ℝ))]
    have hsq_abs : (δ * Real.sqrt (r : ℝ)) ^ 2 ≤
        |(numSolutions a b c f g s r : ℝ)
          - (r : ℝ) * (s : ℝ) / (Fintype.card F : ℝ)| ^ 2 := sq_le_sq' hlow hc
    rw [sq_abs] at hsq_abs
    rwa [mul_pow, Real.sq_sqrt hr0] at hsq_abs
  calc ((badSet a b f g s r δ).card : ℝ) * (δ ^ 2 * (r : ℝ))
      = ∑ _c ∈ badSet a b f g s r δ, (δ ^ 2 * (r : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ c ∈ badSet a b f g s r δ, ((numSolutions a b c f g s r : ℝ)
          - (r : ℝ) * (s : ℝ) / (Fintype.card F : ℝ)) ^ 2 :=
        Finset.sum_le_sum hpt
    _ ≤ ∑ c : Fˣ, ((numSolutions a b c f g s r : ℝ)
          - (r : ℝ) * (s : ℝ) / (Fintype.card F : ℝ)) ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · exact Finset.filter_subset _ _
        · intro c _ _; positivity

/-- A second-moment bound of `|F| * r` yields at most `|F| / δ ^ 2` exceptional nonzero targets,
outside which the count deviation is less than `δ * √r`. See [VanDamShparlinski2008]. -/
theorem lemma2_typical_count_of_second_moment {F : Type*} [Field F] [Fintype F]
    (a b f g : Fˣ) (r : ℕ) (δ : ℝ) (hr : 1 ≤ r) (hδ : 0 < δ)
    (hW : (∑ c : Fˣ, ((numSolutions a b c f g (orderOf f) r : ℝ)
          - (r : ℝ) * (orderOf f : ℝ) / (Fintype.card F : ℝ)) ^ 2)
        ≤ (Fintype.card F : ℝ) * (r : ℝ)) :
    ∃ bad : Finset Fˣ,
      (bad.card : ℝ) ≤ (Fintype.card F : ℝ) / δ ^ 2 ∧
      ∀ c : Fˣ, c ∉ bad →
        |(numSolutions a b c f g (orderOf f) r : ℝ)
            - (r : ℝ) * (orderOf f : ℝ) / (Fintype.card F : ℝ)|
          < δ * Real.sqrt (r : ℝ) := by
  classical
  refine ⟨badSet a b f g (orderOf f) r δ, ?_, ?_⟩
  · have hcheb := badSet_card_mul_le_sum_sq a b f g (orderOf f) r δ hδ
    have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
    have hδ2 : (0 : ℝ) < δ ^ 2 := by positivity
    have hdr : (0 : ℝ) < δ ^ 2 * (r : ℝ) := mul_pos hδ2 hrpos
    rw [le_div_iff₀ hδ2]
    calc ((badSet a b f g (orderOf f) r δ).card : ℝ) * δ ^ 2
        = (((badSet a b f g (orderOf f) r δ).card : ℝ) * (δ ^ 2 * (r : ℝ))) / (r : ℝ) := by
          field_simp
      _ ≤ ((Fintype.card F : ℝ) * (r : ℝ)) / (r : ℝ) := by
          exact div_le_div_of_nonneg_right (le_trans hcheb hW) (le_of_lt hrpos)
      _ = (Fintype.card F : ℝ) := by field_simp
  · intro c hc
    simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hc
    exact hc

/-- Under the stated uniform deviation estimate, a scan length above the given `K`-dependent
threshold and at most `orderOf g` guarantees a solution in the box. See
[VanDamShparlinski2008]. -/
theorem corollary1_solvable_of_bound {F : Type*} [Field F] [Fintype F]
    (a b c f g : Fˣ) (K : ℝ) (hK : 0 < K)
    (hbound : ∀ r : ℕ, 1 ≤ r → r ≤ orderOf g →
      |(numSolutions a b c f g (orderOf f) r : ℝ)
          - (r : ℝ) * (orderOf f : ℝ) / ((Fintype.card F : ℝ) - 1)|
        ≤ K * Real.sqrt (Fintype.card F) * Real.log (Fintype.card F))
    (r : ℕ)
    (hlow : (2 * K + 2) * (Fintype.card F : ℝ) * Real.sqrt (Fintype.card F : ℝ)
        / (orderOf f : ℝ) * Real.log (Fintype.card F : ℝ) ≤ (r : ℝ))
    (hup : (r : ℝ) ≤ (orderOf g : ℝ)) :
    ∃ x y : ℕ, x < orderOf f ∧ y < r ∧
      (a : F) * (f : F) ^ x + (b : F) * (g : F) ^ y = (c : F) := by
  classical
  have hq2 : 1 < Fintype.card F := Fintype.one_lt_card
  have hq1 : (1 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hq2
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) := by linarith
  have hqneg : (0 : ℝ) < (Fintype.card F : ℝ) - 1 := by linarith
  have hsqrtpos : (0 : ℝ) < Real.sqrt (Fintype.card F : ℝ) :=
    Real.sqrt_pos.mpr hqpos
  have hlogpos : (0 : ℝ) < Real.log (Fintype.card F : ℝ) := Real.log_pos hq1
  haveI : Finite Fˣ := Finite.of_injective (Units.val) (fun _ _ h => Units.ext h)
  have hsNat : 0 < orderOf f := orderOf_pos f
  have hspos : (0 : ℝ) < (orderOf f : ℝ) := by exact_mod_cast hsNat
  have hvalpos : 0 < (2 * K + 2) * (Fintype.card F : ℝ) * Real.sqrt (Fintype.card F : ℝ)
      / (orderOf f : ℝ) * Real.log (Fintype.card F : ℝ) := by positivity
  have hrposReal : (0 : ℝ) < (r : ℝ) := lt_of_lt_of_le hvalpos hlow
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · rw [h] at hrposReal; norm_num at hrposReal
    · exact h
  have hrle : r ≤ orderOf g := by exact_mod_cast hup
  by_contra hno
  push_neg at hno
  have hzero : numSolutions a b c f g (orderOf f) r = 0 :=
    (numSolutions_eq_zero_iff a b c f g (orderOf f) r).mpr hno
  have hb := hbound r hr1 hrle
  have hmain_nonneg : (0 : ℝ) ≤
      (r : ℝ) * (orderOf f : ℝ) / ((Fintype.card F : ℝ) - 1) := by positivity
  have hb' : (r : ℝ) * (orderOf f : ℝ) / ((Fintype.card F : ℝ) - 1)
      ≤ K * Real.sqrt (Fintype.card F : ℝ) * Real.log (Fintype.card F : ℝ) := by
    rw [hzero, Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg hmain_nonneg] at hb
    exact hb
  have hmul : (2 * K + 2) * (Fintype.card F : ℝ) * Real.sqrt (Fintype.card F : ℝ)
      * Real.log (Fintype.card F : ℝ) ≤ (r : ℝ) * (orderOf f : ℝ) := by
    have he : (2 * K + 2) * (Fintype.card F : ℝ) * Real.sqrt (Fintype.card F : ℝ)
        / (orderOf f : ℝ) * Real.log (Fintype.card F : ℝ)
        = (2 * K + 2) * (Fintype.card F : ℝ) * Real.sqrt (Fintype.card F : ℝ)
          * Real.log (Fintype.card F : ℝ) / (orderOf f : ℝ) := by ring
    rw [he] at hlow
    exact (div_le_iff₀ hspos).mp hlow
  have hlowmain : (2 * K + 2) * Real.sqrt (Fintype.card F : ℝ)
        * Real.log (Fintype.card F : ℝ)
      ≤ (r : ℝ) * (orderOf f : ℝ) / ((Fintype.card F : ℝ) - 1) := by
    rw [le_div_iff₀ hqneg]
    have hCnn : (0 : ℝ) ≤ (2 * K + 2) * Real.sqrt (Fintype.card F : ℝ)
        * Real.log (Fintype.card F : ℝ) := by positivity
    nlinarith [hmul, hCnn]
  have hKcontra : (2 * K + 2) * Real.sqrt (Fintype.card F : ℝ)
        * Real.log (Fintype.card F : ℝ)
      ≤ K * Real.sqrt (Fintype.card F : ℝ) * Real.log (Fintype.card F : ℝ) :=
    le_trans hlowmain hb'
  have hposprod : 0 < Real.sqrt (Fintype.card F : ℝ) * Real.log (Fintype.card F : ℝ) :=
    mul_pos hsqrtpos hlogpos
  nlinarith [hKcontra, hposprod]

/-- Under the supplied second-moment estimate and field-size condition, a scan length between
the typical threshold and `orderOf g` yields solutions for all but at most `ε * |F|` nonzero
targets. See [VanDamShparlinski2008]. -/
theorem corollary2_typical_solvable_of_second_moment {F : Type*} [Field F] [Fintype F]
    (a b f g : Fˣ)
    (hW : ∀ r : ℕ, 1 ≤ r → r ≤ orderOf g →
      (∑ c : Fˣ, ((numSolutions a b c f g (orderOf f) r : ℝ)
          - (r : ℝ) * (orderOf f : ℝ) / (Fintype.card F : ℝ)) ^ 2)
        ≤ (Fintype.card F : ℝ) * (r : ℝ))
    (ε : ℝ) (hε : 0 < ε) (hQ : Real.exp (1 / ε) ≤ (Fintype.card F : ℝ))
    (r : ℕ)
    (hlow : (Fintype.card F : ℝ) ^ 2 / (orderOf f : ℝ) ^ 2
        * Real.log (Fintype.card F : ℝ) ≤ (r : ℝ))
    (hup : (r : ℝ) ≤ (orderOf g : ℝ)) :
    ∃ bad : Finset Fˣ,
      (bad.card : ℝ) ≤ ε * (Fintype.card F : ℝ) ∧
      ∀ c : Fˣ, c ∉ bad →
        ∃ x y : ℕ, x < orderOf f ∧ y < r ∧
          (a : F) * (f : F) ^ x + (b : F) * (g : F) ^ y = (c : F) := by
  classical
  have hq2 : 1 < Fintype.card F := Fintype.one_lt_card
  have hq1 : (1 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hq2
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) := by linarith
  have hlogpos : (0 : ℝ) < Real.log (Fintype.card F : ℝ) := Real.log_pos hq1
  have hlogge : 1 / ε ≤ Real.log (Fintype.card F : ℝ) := by
    calc 1 / ε = Real.log (Real.exp (1 / ε)) := (Real.log_exp _).symm
      _ ≤ Real.log (Fintype.card F : ℝ) := Real.log_le_log (Real.exp_pos _) hQ
  haveI : Finite Fˣ := Finite.of_injective (Units.val) (fun _ _ h => Units.ext h)
  have hsNat : 0 < orderOf f := orderOf_pos f
  have hspos : (0 : ℝ) < (orderOf f : ℝ) := by exact_mod_cast hsNat
  have hrposReal : (0 : ℝ) < (r : ℝ) := by
    have hnn : 0 < (Fintype.card F : ℝ) ^ 2 / (orderOf f : ℝ) ^ 2
        * Real.log (Fintype.card F : ℝ) := by positivity
    linarith
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · rw [h] at hrposReal; norm_num at hrposReal
    · exact h
  have hrle : r ≤ orderOf g := by exact_mod_cast hup
  obtain ⟨bad, hbadcard, hbad⟩ :=
    lemma2_typical_count_of_second_moment a b f g r
      (Real.sqrt (Real.log (Fintype.card F : ℝ)))
      hr1 (Real.sqrt_pos.mpr hlogpos) (hW r hr1 hrle)
  refine ⟨bad, ?_, ?_⟩
  · have hdelta_sq : (Real.sqrt (Real.log (Fintype.card F : ℝ))) ^ 2
        = Real.log (Fintype.card F : ℝ) :=
      Real.sq_sqrt (le_of_lt hlogpos)
    rw [hdelta_sq] at hbadcard
    have hle : (Fintype.card F : ℝ) / Real.log (Fintype.card F : ℝ)
        ≤ ε * (Fintype.card F : ℝ) := by
      have hone : 1 ≤ ε * Real.log (Fintype.card F : ℝ) := by
        have h := (div_le_iff₀ hε).mp hlogge
        nlinarith [h]
      rw [div_le_iff₀ hlogpos]
      nlinarith [hone, hqpos]
    exact le_trans hbadcard hle
  · intro c hc
    have hc' := hbad c hc
    have hrsq : Real.sqrt (r : ℝ) * Real.sqrt (Real.log (Fintype.card F : ℝ))
        ≤ (r : ℝ) * (orderOf f : ℝ) / (Fintype.card F : ℝ) := by
      have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
      have hsqrtprod_eq : Real.sqrt (r : ℝ) * Real.sqrt (Real.log (Fintype.card F : ℝ))
          = Real.sqrt ((r : ℝ) * Real.log (Fintype.card F : ℝ)) :=
        (Real.sqrt_mul hr0 _).symm
      rw [hsqrtprod_eq, Real.sqrt_le_iff]
      refine ⟨?_, ?_⟩
      · positivity
      · have hkey : (Fintype.card F : ℝ) ^ 2 * Real.log (Fintype.card F : ℝ)
            ≤ (r : ℝ) * (orderOf f : ℝ) ^ 2 := by
          have he : (Fintype.card F : ℝ) ^ 2 / (orderOf f : ℝ) ^ 2
              * Real.log (Fintype.card F : ℝ)
              = (Fintype.card F : ℝ) ^ 2 * Real.log (Fintype.card F : ℝ)
                / (orderOf f : ℝ) ^ 2 := by ring
          rw [he] at hlow
          exact (div_le_iff₀ (by positivity : (0 : ℝ) < (orderOf f : ℝ) ^ 2)).mp hlow
        have hsq : ((r : ℝ) * (orderOf f : ℝ) / (Fintype.card F : ℝ)) ^ 2
            = (r : ℝ) * ((r : ℝ) * (orderOf f : ℝ) ^ 2) / (Fintype.card F : ℝ) ^ 2 := by
          ring
        rw [hsq]
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < (Fintype.card F : ℝ) ^ 2)]
        nlinarith [hkey, hr0]
    have hNpos : (0 : ℝ) < (numSolutions a b c f g (orderOf f) r : ℝ) := by
      have h1 : -(Real.sqrt (Real.log (Fintype.card F : ℝ)) * Real.sqrt (r : ℝ))
          < (numSolutions a b c f g (orderOf f) r : ℝ)
            - (r : ℝ) * (orderOf f : ℝ) / (Fintype.card F : ℝ) := (abs_lt.mp hc').1
      have hrsq' : Real.sqrt (Real.log (Fintype.card F : ℝ)) * Real.sqrt (r : ℝ)
          ≤ (r : ℝ) * (orderOf f : ℝ) / (Fintype.card F : ℝ) := by
        rw [mul_comm]; exact hrsq
      linarith [h1, hrsq']
    have hNposNat : 0 < numSolutions a b c f g (orderOf f) r := by
      exact_mod_cast hNpos
    exact exists_of_numSolutions_pos a b c f g (orderOf f) r hNposNat

end Qatlib.Papers.ExpCongruence08.MainResults
