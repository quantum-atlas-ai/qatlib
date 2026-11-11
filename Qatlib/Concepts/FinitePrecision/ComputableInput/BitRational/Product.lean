/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.RationalData

/-!
# Correctness and bounds for rational products

This module verifies signed rational construction and the counted rational multiplication and
division procedures. The results identify their rational values, bound the output height width
by the sum of input widths, and establish the gate cap `binomialRatOpGateCap`.

For background on classical computation and its resource models, see [KitaevShenVyalyi2002].

## Main statements

* `binomial_signed_rat`: correctness, width, and gate bounds for signed reduction.
* `binomial_rat_mul_bits`: correctness and bounds for rational multiplication.
* `binomial_rat_div_bits`: correctness and bounds for rational division.

## References

* [Kitaev, Shen and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

/-- Recover an integer from its sign test and natural absolute value using
`binomialSignedMagnitude`. -/
private theorem signed_abs (a : ℤ) :
    binomialSignedMagnitude (decide (a < 0)) a.natAbs = a := by
  by_cases ha : a < 0
  · have h := Int.natAbs_of_nonneg (by omega : 0 ≤ -a)
    simp only [Int.natAbs_neg] at h
    simp only [binomialSignedMagnitude,decide_eq_true ha,if_true]
    omega
  · simp [binomialSignedMagnitude,ha,Int.natAbs_of_nonneg (by omega : 0 ≤ a)]

/-- The natural absolute value of a signed magnitude is its original magnitude. -/
private theorem magnitude_abs (s : Bool) (n : ℕ) :
    (binomialSignedMagnitude s n).natAbs = n := by
  cases s <;> simp [binomialSignedMagnitude]

/-- Negation preserves the rational height `binomialRatHeight`. -/
private theorem height_neg (q : ℚ) : binomialRatHeight (-q) = binomialRatHeight q := by
  simp [binomialRatHeight]

/-- Signed rational reduction returns `mkRat a d`, with height width at most `max 1 w` and gate
count at most `w * (44 * w ^ 2 + 2 * w) + 44 * w ^ 2`, where `w` is the larger input size. -/
theorem binomial_signed_rat (a : ℤ) (d : ℕ) :
    let w := max a.natAbs.size d.size
    let r := binomialSignedRat a d
    r.1 = mkRat a d ∧ (binomialRatHeight r.1).size ≤ max 1 w ∧
    r.2 ≤ w*(44*w^2+2*w)+44*w^2 := by
  by_cases hd : d = 0
  · simp [binomialSignedRat,hd,binomialRatHeight]
  let w := max a.natAbs.size d.size
  let q := binomialReducedRat a.natAbs d (Nat.pos_of_ne_zero hd)
  have hr := binomial_reduce_fraction a.natAbs d (Nat.pos_of_ne_zero hd)
  have hn := (Nat.size_le_size hr.2.2.2.1).trans (le_max_left a.natAbs.size d.size)
  have hb := (Nat.size_le_size hr.2.2.2.2.1).trans (le_max_right a.natAbs.size d.size)
  have hh : (binomialRatHeight q.1).size ≤ w := by
    simp only [q,binomialReducedRat,binomialRatHeight,Int.natAbs_natCast]
    rcases le_total (binomialReduceFraction a.natAbs d).1.1
        (binomialReduceFraction a.natAbs d).1.2 with h | h
    · rw [max_eq_right h]; exact hb
    · rw [max_eq_left h]; exact hn
  have hv : (if a < 0 then -q.1 else q.1) = mkRat a d := by
    dsimp only [q]
    rw [binomial_reduced_rat]
    have ha := signed_abs a
    simp only [binomialSignedMagnitude,decide_eq_true_eq] at ha
    split_ifs with hs
    · rw [Rat.neg_mkRat]
      simp only [if_pos hs] at ha
      rw [ha]
    · simp only [if_neg hs] at ha
      rw [ha]
  change (binomialSignedRat a d).1 = _ ∧ _
  simp only [binomialSignedRat,dif_neg hd]
  change (if a < 0 then -q.1 else q.1) = _ ∧
    (binomialRatHeight (if a < 0 then -q.1 else q.1)).size ≤ max 1 w ∧ q.2 ≤ _
  refine ⟨hv,?_,hr.2.2.2.2.2⟩
  split_ifs <;> simpa only [height_neg] using hh.trans (le_max_right 1 w)

end Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

/-- The binary size of a natural product is at most the sum of the factor sizes. -/
private theorem size_product (a b : ℕ) : (a*b).size ≤ a.size+b.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact (Nat.mul_le_mul_left a (Nat.lt_size_self b).le).trans_lt
    (mul_lt_mul_of_pos_right (Nat.lt_size_self a) (by positivity))

/-- The height width of a rational is at least one. -/
private theorem width_pos (a : ℚ) : 1 ≤ (binomialRatHeight a).size := by
  have h : 1 ≤ binomialRatHeight a := a.den_pos.trans_le (le_max_right _ _)
  simpa using Nat.size_le_size h

/-- The binary size of the absolute numerator is at most the rational height width. -/
private theorem width_num (a : ℚ) : a.num.natAbs.size ≤ (binomialRatHeight a).size :=
  Nat.size_le_size (le_max_left _ _)

/-- The binary size of the denominator is at most the rational height width. -/
private theorem width_den (a : ℚ) : a.den.size ≤ (binomialRatHeight a).size :=
  Nat.size_le_size (le_max_right _ _)

/-- Computing two natural products and reducing their signed ratio gives the expected rational,
with height width at most `H` and total gates at most `binomialRatOpGateCap H`, under the
stated size bounds. -/
private theorem product_pair (s : Bool) (a b c d H : ℕ)
    (h1 : a.size+b.size ≤ H) (h2 : c.size+d.size ≤ H) (hp : 1 ≤ H) :
    let n := binomialBitMul a.bits b.bits
    let m := binomialBitMul c.bits d.bits
    let q :=
        binomialSignedRat (binomialSignedMagnitude s (binomialBitValue n.1)) (binomialBitValue m.1)
    q.1 = mkRat (binomialSignedMagnitude s (a*b)) (c*d) ∧
    (binomialRatHeight q.1).size ≤ H ∧ n.2+m.2+1+q.2 ≤ binomialRatOpGateCap H := by
  let n := binomialBitMul a.bits b.bits
  let m := binomialBitMul c.bits d.bits
  have hn := binomial_bit_mul a.bits b.bits
  have hm := binomial_bit_mul c.bits d.bits
  simp only [binomial_bit_value_bits,Nat.size_eq_bits_len] at hn hm
  change binomialBitValue n.1 = a*b ∧ _ ∧ n.2 = _ at hn
  change binomialBitValue m.1 = c*d ∧ _ ∧ m.2 = _ at hm
  have hq :=
      binomial_signed_rat (binomialSignedMagnitude s (binomialBitValue n.1)) (binomialBitValue m.1)
  simp only [magnitude_abs,hn.1,hm.1] at hq
  have hw : max (a*b).size (c*d).size ≤ H :=
    max_le ((size_product a b).trans h1) ((size_product c d).trans h2)
  have hg : max (a*b).size (c*d).size * (44*(max (a*b).size (c*d).size)^2+
      2*max (a*b).size (c*d).size)+44*(max (a*b).size (c*d).size)^2 ≤
      H*(44*H^2+2*H)+44*H^2 := by gcongr
  have hn2 : n.2 ≤ 11*H^2 := by
    have haa : a.size ≤ H := by omega
    have hab : b.size ≤ H := by omega
    have hsq := Nat.mul_self_le_mul_self haa
    have hab' := Nat.mul_le_mul haa hab
    nlinarith [hn.2.2]
  have hm2 : m.2 ≤ 11*H^2 := by
    have hca : c.size ≤ H := by omega
    have hcd : d.size ≤ H := by omega
    have hsq := Nat.mul_self_le_mul_self hca
    have hcd' := Nat.mul_le_mul hca hcd
    nlinarith [hm.2.2]
  have hnv : binomialBitValue (binomialBitMul a.bits b.bits).1 = a*b := hn.1
  have hmv : binomialBitValue (binomialBitMul c.bits d.bits).1 = c*d := hm.1
  (try dsimp only)
  rw [hnv,hmv]
  refine ⟨hq.1,hq.2.1.trans (max_le hp hw),?_⟩
  have hcost := hq.2.2.trans hg
  unfold binomialRatOpGateCap
  change n.2+m.2+1+(binomialSignedRat (binomialSignedMagnitude s (a*b)) (c*d)).2 ≤ _
  omega

/-- Multiplying two signed natural ratios multiplies their magnitudes and combines their sign
bits by Boolean exclusive-or. -/
private theorem signed_ratio_mul (s t : Bool) (a b c d : ℕ) :
    (binomialSignedMagnitude (Bool.xor s t) (a*c) : ℚ)/(b*d : ℕ) =
      ((binomialSignedMagnitude s a : ℚ)/(b : ℚ))*
        ((binomialSignedMagnitude t c : ℚ)/(d : ℚ)) := by
  cases s <;> cases t <;> simp [binomialSignedMagnitude,div_eq_mul_inv] <;> ring

/-- Dividing two signed natural ratios forms the cross products and combines their sign bits by
Boolean exclusive-or. -/
private theorem signed_ratio_div (s t : Bool) (a b c d : ℕ) :
    (binomialSignedMagnitude (Bool.xor s t) (a*d) : ℚ)/(b*c : ℕ) =
      ((binomialSignedMagnitude s a : ℚ)/(b : ℚ))/
        ((binomialSignedMagnitude t c : ℚ)/(d : ℚ)) := by
  cases s <;> cases t <;> simp [binomialSignedMagnitude,div_eq_mul_inv] <;> ring

end Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

/-- Counted rational multiplication returns `a * b`, with height width at most the sum of input
height widths and gate count bounded by `binomialRatOpGateCap` at that sum. -/
theorem binomial_rat_mul_bits (a b : ℚ) :
    let H := (binomialRatHeight a).size+(binomialRatHeight b).size
    let r := binomialRatMulBits a b
    r.1 = a*b ∧ (binomialRatHeight r.1).size ≤ H ∧ r.2 ≤ binomialRatOpGateCap H := by
  let H := (binomialRatHeight a).size+(binomialRatHeight b).size
  let s := Bool.xor (decide (a.num < 0)) (decide (b.num < 0))
  have h := product_pair s a.num.natAbs b.num.natAbs a.den b.den H
    (Nat.add_le_add (width_num a) (width_num b))
    (Nat.add_le_add (width_den a) (width_den b)) (by have := width_pos a; dsimp [H]; omega)
  refine ⟨?_,h.2.1,h.2.2⟩
  calc
    _ = mkRat (binomialSignedMagnitude s (a.num.natAbs*b.num.natAbs)) (a.den*b.den) := h.1
    _ = a*b := by
      rw [Rat.mkRat_eq_div,signed_ratio_mul,signed_abs,signed_abs,a.num_div_den,b.num_div_den]

/-- Counted rational division returns `a / b`, with height width at most the sum of input height
widths and gate count bounded by `binomialRatOpGateCap` at that sum. -/
theorem binomial_rat_div_bits (a b : ℚ) :
    let H := (binomialRatHeight a).size+(binomialRatHeight b).size
    let r := binomialRatDivBits a b
    r.1 = a/b ∧ (binomialRatHeight r.1).size ≤ H ∧ r.2 ≤ binomialRatOpGateCap H := by
  let H := (binomialRatHeight a).size+(binomialRatHeight b).size
  let s := Bool.xor (decide (a.num < 0)) (decide (b.num < 0))
  have h := product_pair s a.num.natAbs b.den a.den b.num.natAbs H
    (Nat.add_le_add (width_num a) (width_den b))
    (Nat.add_le_add (width_den a) (width_num b)) (by have := width_pos a; dsimp [H]; omega)
  refine ⟨?_,h.2.1,h.2.2⟩
  calc
    _ = mkRat (binomialSignedMagnitude s (a.num.natAbs*b.den)) (a.den*b.num.natAbs) := h.1
    _ = a/b := by
      rw [Rat.mkRat_eq_div,signed_ratio_div,signed_abs,signed_abs,a.num_div_den,b.num_div_den]

end Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational
