/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.Product

/-!
# Correctness and costs of rational addition

This module verifies signed-magnitude addition and uses the bit-level arithmetic routines to
establish rational addition and subtraction specifications. The results track the bit size of
rational height and an explicit gate-count cap, providing arithmetic components for the
computational setting of [KitaevShenVyalyi2002].

The height parameter `H` combines the two input height bit sizes with one additional bit. Both
`binomialRatAddBits` and `binomialRatSubBits` return the exact rational result with output
height bit size at most `H` and cost bounded by `binomialRatAddGateCap H`.

## Main statements

* `binomial_signed_add_bits`: signed-magnitude addition is correct with a linear width-based
  cost bound.
* `binomial_rat_add_bits`: exact rational addition satisfies the height and gate-count bounds.
* `binomial_rat_sub_bits`: exact rational subtraction satisfies the same bounds.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

/-- The absolute natural value of a signed magnitude is its magnitude. -/
private theorem magnitude_abs (s : Bool) (n : ℕ) :
    (binomialSignedMagnitude s n).natAbs = n := by
  cases s <;> simp [binomialSignedMagnitude]

/-- Signed-magnitude encoding with a fixed sign preserves addition of natural magnitudes. -/
private theorem same_sum (s : Bool) (a b : ℕ) :
    binomialSignedMagnitude s (a+b) = binomialSignedMagnitude s a+binomialSignedMagnitude s b := by
  cases s <;> simp [binomialSignedMagnitude,add_comm]

/-- For opposite signs and `a ≤ b`, encoding `b - a` with the second sign equals the sum of the
two signed magnitudes. -/
private theorem opposite_sub (s t : Bool) (a b : ℕ) (hs : s ≠ t) (hab : a ≤ b) :
    binomialSignedMagnitude t (b-a) = binomialSignedMagnitude s a+binomialSignedMagnitude t b := by
  cases s <;> cases t <;> simp_all [binomialSignedMagnitude] <;> omega

/-- Signed bit-list addition returns the sum of the encoded integers, bounds its absolute value
by the sum of magnitudes, and uses at most `1 + 11 * max xs.length ys.length` gates. -/
theorem binomial_signed_add_bits (s t : Bool) (xs ys : List Bool) :
    let r := binomialSignedAddBits s t xs ys
    r.1 = binomialSignedMagnitude s (binomialBitValue xs)+
      binomialSignedMagnitude t (binomialBitValue ys) ∧
    r.1.natAbs ≤ binomialBitValue xs+binomialBitValue ys ∧
    r.2 ≤ 1+11*max xs.length ys.length := by
  let k := max xs.length ys.length
  have core : (binomialSignedAddBits s t xs ys).1 =
      binomialSignedMagnitude s (binomialBitValue xs)+binomialSignedMagnitude t (binomialBitValue ys) ∧
      (binomialSignedAddBits s t xs ys).2 ≤ 1+11*k := by
    by_cases hst : Bool.xor s t = true
    · have hne : s ≠ t := by intro he; subst t; cases s <;> simp_all
      let cmp := binomialBitCompare k xs ys true
      have hcmp := (binomial_bit_compare k xs ys true (le_max_left _ _) (le_max_right _ _)).1
      have hcg := (binomial_bit_compare k xs ys true (le_max_left _ _) (le_max_right _ _)).2
      change (cmp.1 = true ↔ _) at hcmp
      change cmp.2 = 5*k at hcg
      by_cases hc : cmp.1 = true
      · have hab : binomialBitValue xs ≤ binomialBitValue ys := by
          have h := hcmp.mp hc
          simpa only [Bool.toNat_true,Nat.add_le_add_iff_right] using h
        obtain ⟨hv,_,_,hg⟩ := binomial_bit_subtract k ys xs (le_max_right _ _) (le_max_left _ _) hab
        have he : binomialSignedAddBits s t xs ys =
            (binomialSignedMagnitude t (binomialBitValue (binomialBitSubtract k ys xs true).1.1),
              1+cmp.2+(binomialBitSubtract k ys xs true).2) := by
          dsimp only [cmp,k] at hc
          simp only [binomialSignedAddBits,if_pos hst,if_pos hc]
          rfl
        rw [he]
        exact ⟨by rw [hv]; exact opposite_sub s t _ _ hne hab,by omega⟩
      · have hab : binomialBitValue ys ≤ binomialBitValue xs := by
          have h := mt hcmp.mpr hc
          simp only [Bool.toNat_true,Nat.add_le_add_iff_right] at h
          omega
        obtain ⟨hv,_,_,hg⟩ := binomial_bit_subtract k xs ys (le_max_left _ _) (le_max_right _ _) hab
        have he : binomialSignedAddBits s t xs ys =
            (binomialSignedMagnitude s (binomialBitValue (binomialBitSubtract k xs ys true).1.1),
              1+cmp.2+(binomialBitSubtract k xs ys true).2) := by
          dsimp only [cmp,k] at hc
          simp only [binomialSignedAddBits,if_pos hst,if_neg hc]
          rfl
        rw [he]
        refine ⟨?_,by omega⟩
        rw [hv]
        simpa only [add_comm] using opposite_sub t s _ _ hne.symm hab
    · have heq : s = t := by cases s <;> cases t <;> simp_all
      subst t
      obtain ⟨hv,_,hg⟩ := binomial_bit_add k xs ys false (le_max_left _ _) (le_max_right _ _)
      simp only [Bool.toNat_false,add_zero] at hv
      simp only [binomialSignedAddBits,if_neg hst]
      refine ⟨?_,by dsimp [k] at hg ⊢; omega⟩
      rw [hv,same_sum]
  refine ⟨core.1,?_,core.2⟩
  rw [core.1]
  simpa only [magnitude_abs] using Int.natAbs_add_le
    (binomialSignedMagnitude s (binomialBitValue xs)) (binomialSignedMagnitude t (binomialBitValue ys))

end Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

/-- The bit size of a natural-number product is at most the sum of the operand bit sizes. -/
private theorem size_product (a b : ℕ) : (a*b).size ≤ a.size+b.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact (Nat.mul_le_mul_left a (Nat.lt_size_self b).le).trans_lt
    (mul_lt_mul_of_pos_right (Nat.lt_size_self a) (by positivity))

/-- The bit size of a natural-number sum is at most one plus the maximum operand bit size. -/
private theorem size_sum (a b : ℕ) : (a+b).size ≤ 1+max a.size b.size := by
  have ha := Nat.size_le.mp (le_max_left a.size b.size)
  have hb := Nat.size_le.mp (le_max_right a.size b.size)
  apply Nat.size_le.mpr
  rw [pow_add]
  norm_num only [pow_one]
  omega

/-- The bit sizes of a rational number's absolute numerator and denominator are both bounded by
the bit size of its rational height. -/
private theorem widths (a : ℚ) : a.num.natAbs.size ≤ (binomialRatHeight a).size ∧
    a.den.size ≤ (binomialRatHeight a).size :=
  ⟨Nat.size_le_size (le_max_left _ _),Nat.size_le_size (le_max_right _ _)⟩

/-- Encoding an integer's absolute value with the Boolean test for negativity recovers the
integer. -/
private theorem signed_abs (a : ℤ) : binomialSignedMagnitude (decide (a < 0)) a.natAbs = a := by
  by_cases ha : a < 0
  · have h := Int.natAbs_of_nonneg (by omega : 0 ≤ -a)
    simp only [Int.natAbs_neg] at h
    simp only [binomialSignedMagnitude,decide_eq_true ha,if_true]
    omega
  · simp [binomialSignedMagnitude,ha,Int.natAbs_of_nonneg (by omega : 0 ≤ a)]

/-- Signed-magnitude encoding of a natural product equals the signed first factor multiplied by
the second factor. -/
private theorem signed_scale (s : Bool) (a b : ℕ) :
    binomialSignedMagnitude s (a*b) = binomialSignedMagnitude s a*(b : ℤ) := by
  cases s <;> simp [binomialSignedMagnitude]

/-- If both natural operands have bit size at most `W`, bit-list multiplication costs at most
`11 * W ^ 2`. -/
private theorem mul_cost (a b W : ℕ) (ha : a.size ≤ W) (hb : b.size ≤ W) :
    (binomialBitMul a.bits b.bits).2 ≤ 11*W^2 := by
  have h := (binomial_bit_mul a.bits b.bits).2.2
  simp only [Nat.size_eq_bits_len] at h
  have hs := Nat.mul_self_le_mul_self ha
  have hp := Nat.mul_le_mul ha hb
  nlinarith

/-- Bit-level rational addition returns `a + b`, with height bit size at most `H` and gate count
at most `binomialRatAddGateCap H`, where `H` is one plus the sum of the input height bit
sizes. -/
theorem binomial_rat_add_bits (a b : ℚ) :
    let H := 1+(binomialRatHeight a).size+(binomialRatHeight b).size
    let r := binomialRatAddBits a b
    r.1 = a+b ∧ (binomialRatHeight r.1).size ≤ H ∧ r.2 ≤ binomialRatAddGateCap H := by
  let W := 1+(binomialRatHeight a).size+(binomialRatHeight b).size
  obtain ⟨ha,hda⟩ := widths a
  obtain ⟨hb,hdb⟩ := widths b
  dsimp only [binomialRatAddBits]
  generalize hx : binomialBitMul a.num.natAbs.bits b.den.bits = x
  generalize hy : binomialBitMul b.num.natAbs.bits a.den.bits = y
  generalize hd : binomialBitMul a.den.bits b.den.bits = den
  generalize hn : binomialSignedAddBits (decide (a.num < 0)) (decide (b.num < 0)) x.1 y.1 = num
  generalize hq : binomialSignedRat num.1 (binomialBitValue den.1) = q
  have xs := binomial_bit_mul a.num.natAbs.bits b.den.bits
  have ys := binomial_bit_mul b.num.natAbs.bits a.den.bits
  have ds := binomial_bit_mul a.den.bits b.den.bits
  rw [hx] at xs
  rw [hy] at ys
  rw [hd] at ds
  simp only [binomial_bit_value_bits,Nat.size_eq_bits_len] at xs ys ds
  have ns := binomial_signed_add_bits (decide (a.num < 0)) (decide (b.num < 0)) x.1 y.1
  rw [hn] at ns
  have qs := binomial_signed_rat num.1 (binomialBitValue den.1)
  rw [hq] at qs
  have nv : num.1 = a.num*b.den+b.num*a.den := by
    rw [ns.1,xs.1,ys.1,signed_scale,signed_scale,signed_abs,signed_abs]
  have xp : (a.num.natAbs*b.den).size ≤ (binomialRatHeight a).size+(binomialRatHeight b).size :=
    (size_product _ _).trans (Nat.add_le_add ha hdb)
  have yp : (b.num.natAbs*a.den).size ≤ (binomialRatHeight a).size+(binomialRatHeight b).size := by
    have h := (size_product b.num.natAbs a.den).trans (Nat.add_le_add hb hda)
    omega
  have dp : (binomialBitValue den.1).size ≤ W := by
    rw [ds.1]
    have h := (size_product a.den b.den).trans (Nat.add_le_add hda hdb)
    dsimp [W]
    omega
  have np : num.1.natAbs.size ≤ W := by
    have h := Nat.size_le_size ns.2.1
    rw [xs.1,ys.1] at h
    have hh := size_sum (a.num.natAbs*b.den) (b.num.natAbs*a.den)
    dsimp [W]
    omega
  have wp : max num.1.natAbs.size (binomialBitValue den.1).size ≤ W := max_le np dp
  have qg : q.2 ≤ W*(44*W^2+2*W)+44*W^2 := by
    refine qs.2.2.trans ?_
    gcongr
  have xg : x.2 ≤ 11*W^2 := by
    rw [← hx]
    exact mul_cost _ _ W (by dsimp [W]; omega) (by dsimp [W]; omega)
  have yg : y.2 ≤ 11*W^2 := by
    rw [← hy]
    exact mul_cost _ _ W (by dsimp [W]; omega) (by dsimp [W]; omega)
  have dg : den.2 ≤ 11*W^2 := by
    rw [← hd]
    exact mul_cost _ _ W (by dsimp [W]; omega) (by dsimp [W]; omega)
  have xl : x.1.length ≤ 2*W := by have := xs.2.1; dsimp [W]; omega
  have yl : y.1.length ≤ 2*W := by have := ys.2.1; dsimp [W]; omega
  have ng : num.2 ≤ 1+22*W := by
    have h := ns.2.2
    have hw := max_le xl yl
    omega
  refine ⟨?_,qs.2.1.trans (max_le (by omega) wp),?_⟩
  · rw [qs.1,nv,ds.1]
    exact (Rat.add_def' a b).symm
  · change x.2+y.2+den.2+num.2+q.2 ≤ binomialRatAddGateCap W
    unfold binomialRatAddGateCap
    omega

/-- Bit-level rational subtraction returns `a - b`, with height bit size at most `H` and the
rational-addition gate cap, where `H` is one plus the sum of the input height bit sizes. -/
theorem binomial_rat_sub_bits (a b : ℚ) :
    let H := 1+(binomialRatHeight a).size+(binomialRatHeight b).size
    let r := binomialRatSubBits a b
    r.1 = a-b ∧ (binomialRatHeight r.1).size ≤ H ∧ r.2 ≤ binomialRatAddGateCap H := by
  have h : binomialRatHeight (-b) = binomialRatHeight b := by simp [binomialRatHeight]
  simpa only [binomialRatSubBits,sub_eq_add_neg,h] using binomial_rat_add_bits a (-b)

end Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational
