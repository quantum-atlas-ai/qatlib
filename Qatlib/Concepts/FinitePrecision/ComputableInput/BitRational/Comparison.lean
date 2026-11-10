/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.Arithmetic

set_option autoImplicit false

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

private theorem bit_value_head (xs : List Bool) :
    binomialBitValue xs = (xs.headD false).toNat+2*binomialBitValue xs.tail := by
  cases xs <;> rfl

private theorem compare_step (x y c : Bool) (a b : ℕ) :
    (a+1 ≤ b+(binomialCompareCarry x y c).toNat) ↔
      x.toNat+2*a+1 ≤ y.toNat+2*b+c.toNat := by
  cases x <;> cases y <;> cases c <;> simp [binomialCompareCarry] <;> omega

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

theorem binomial_nat_add (a b : ℕ) : binomialNatAdd a b = (a+b,5*max a.size b.size) := by
  have ha : a.bits.length ≤ max a.size b.size := by
    rw [Nat.size_eq_bits_len]; exact le_max_left _ _
  have hb : b.bits.length ≤ max a.size b.size := by
    rw [Nat.size_eq_bits_len]; exact le_max_right _ _
  obtain ⟨hv,_,hg⟩ := binomial_bit_add (max a.size b.size) a.bits b.bits false ha hb
  simp only [binomial_bit_value_bits,Bool.toNat_false,add_zero] at hv
  exact Prod.ext hv hg

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
