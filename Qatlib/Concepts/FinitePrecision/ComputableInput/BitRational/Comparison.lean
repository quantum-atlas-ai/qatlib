/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.Arithmetic

/-!
# Boolean-list comparison and natural arithmetic

This module proves the comparison invariant for `binomialBitCompare` and verifies the
natural-number addition and comparison wrappers. With inputs fitting in the chosen width, the
comparison routine tests the carry-adjusted inequality and uses five gates per bit. These
Boolean arithmetic routines fit the classical computational framework of [KitaevShenVyalyi2002].

## Main statements

* `binomial_bit_compare`: characterizes the returned comparison bit and exact gate count.
* `binomial_nat_add`: natural addition returns the exact sum with cost determined by the maximum
  input bit size.
* `binomial_nat_le`: natural comparison decides the order relation with the same cost.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

/-- The value of a Boolean list is its defaulted head bit plus twice the value of its tail. -/
private theorem bit_value_head (xs : List Bool) :
    binomialBitValue xs = (xs.headD false).toNat+2*binomialBitValue xs.tail := by
  cases xs <;> rfl

/-- The comparison carry transforms the tail inequality into the corresponding carry-adjusted
inequality for the full binary values. -/
private theorem compare_step (x y c : Bool) (a b : ℕ) :
    (a+1 ≤ b+(binomialCompareCarry x y c).toNat) ↔
      x.toNat+2*a+1 ≤ y.toNat+2*b+c.toNat := by
  cases x <;> cases y <;> cases c <;> simp [binomialCompareCarry] <;> omega

/-- For inputs of length at most `k`, the comparison bit is true exactly when the first value
plus one is at most the second value plus the input carry; the cost is `5 * k`. -/
theorem binomial_bit_compare (k : ℕ) (xs ys : List Bool) (c : Bool)
    (hx : xs.length ≤ k) (hy : ys.length ≤ k) :
    ((binomialBitCompare k xs ys c).1 = true ↔
      binomialBitValue xs+1 ≤ binomialBitValue ys+c.toNat) ∧
    (binomialBitCompare k xs ys c).2 = 5*k := by
  induction k generalizing xs ys c with
  | zero =>
    have hx0 : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hy0 : ys = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst xs; subst ys
    cases c <;> simp [binomialBitCompare,binomialBitValue]
  | succ k ih =>
    have hxt : xs.tail.length ≤ k := by simp only [List.length_tail]; omega
    have hyt : ys.tail.length ≤ k := by simp only [List.length_tail]; omega
    let b := binomialCompareCarry (xs.headD false) (ys.headD false) c
    obtain ⟨hv,hg⟩ := ih xs.tail ys.tail b hxt hyt
    constructor
    · change (binomialBitCompare k xs.tail ys.tail b).1 = true ↔ _
      rw [hv,bit_value_head xs,bit_value_head ys]
      exact compare_step _ _ _ _ _
    · change 5+(binomialBitCompare k xs.tail ys.tail b).2 = _
      omega

/-- Natural bit-level addition returns `(a + b, 5 * max a.size b.size)`. -/
theorem binomial_nat_add (a b : ℕ) : binomialNatAdd a b = (a+b,5*max a.size b.size) := by
  have ha : a.bits.length ≤ max a.size b.size := by
    rw [Nat.size_eq_bits_len]; exact le_max_left _ _
  have hb : b.bits.length ≤ max a.size b.size := by
    rw [Nat.size_eq_bits_len]; exact le_max_right _ _
  obtain ⟨hv,_,hg⟩ := binomial_bit_add (max a.size b.size) a.bits b.bits false ha hb
  simp only [binomial_bit_value_bits,Bool.toNat_false,add_zero] at hv
  exact Prod.ext hv hg

/-- Natural bit-level comparison returns true exactly when `a ≤ b` and costs `5 * max a.size
b.size`. -/
theorem binomial_nat_le (a b : ℕ) :
    ((binomialNatLE a b).1 = true ↔ a ≤ b) ∧
    (binomialNatLE a b).2 = 5*max a.size b.size := by
  have ha : a.bits.length ≤ max a.size b.size := by
    rw [Nat.size_eq_bits_len]; exact le_max_left _ _
  have hb : b.bits.length ≤ max a.size b.size := by
    rw [Nat.size_eq_bits_len]; exact le_max_right _ _
  simpa only [binomialNatLE,binomial_bit_value_bits,Bool.toNat_true,Nat.add_le_add_iff_right] using
    binomial_bit_compare (max a.size b.size) a.bits b.bits true ha hb

end Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational
