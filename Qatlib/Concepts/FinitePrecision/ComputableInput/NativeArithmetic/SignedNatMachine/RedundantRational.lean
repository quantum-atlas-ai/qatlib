/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.NativeArithmetic.SignedNatMachine.RationalDataSize

/-!
# Redundant representations of rational numbers

`Pair` represents a signed value as the difference of two natural numbers. `Frac` represents a
rational value as a quotient of two such pairs, requiring distinct denominator components so
that its interpreted denominator is nonzero.

The operations on pairs and fractions preserve their rational interpretations without requiring
cancellation of common factors. The `Pair.Bound` and `Bound` lemmas track component sizes
through the operations, including total inversion and natural powers.

## Main statements

* `Pair.value_mul`: interpretation of pair multiplication.
* `value_ofRat`: correctness of the embedding of rational numbers.
* `value_inv` and `value_pow`: correctness of inversion and powers.
* `add_bound`, `mul_bound`, and `pow_bound`: growth of representation sizes.

For background on classical computation and resource bounds, see [KitaevShenVyalyi2002].

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine.RedundantRational

/-- A redundant signed representation consisting of positive and negative natural-number
components. -/
abbrev Pair := ℕ × ℕ
namespace Pair

/-- Interpret a pair of natural numbers as their difference in the rationals. -/
def value (x : Pair) : ℚ := (x.1 : ℚ) - x.2
/-- Add redundant signed pairs by adding their positive and negative components separately. -/
def add (x y : Pair) : Pair := (x.1 + y.1, x.2 + y.2)
/-- Negate a redundant signed pair by exchanging its two components. -/
def neg (x : Pair) : Pair := (x.2, x.1)
/-- Multiply redundant signed pairs using the same-sign products for the positive component and
cross products for the negative component. -/
def mul (x y : Pair) : Pair := (x.1 * y.1 + x.2 * y.2, x.1 * y.2 + x.2 * y.1)
/-- Represent an integer by the natural parts of the integer and its negation. -/
def ofInt (n : ℤ) : Pair := (n.toNat, (-n).toNat)

/-- A pair has rational value zero exactly when its two components are equal. -/
theorem value_eq_zero (x : Pair) : value x = 0 ↔ x.1 = x.2 := by
    simp only [value, sub_eq_zero, Nat.cast_inj]

/-- Interpreting componentwise pair addition gives the sum of the interpreted values. -/
theorem value_add (x y : Pair) : value (add x y) = value x + value y := by simp [value, add]; ring

/-- Exchanging the pair components negates its interpreted value. -/
theorem value_neg (x : Pair) : value (neg x) = -value x := by dsimp [value, neg]; ring

/-- Interpreting pair multiplication gives the product of the interpreted values. -/
theorem value_mul (x y : Pair) : value (mul x y) = value x * value y := by simp [value, mul]; ring

/-- The pair constructed from an integer has that integer as its rational value. -/
theorem value_ofInt (n : ℤ) : value (ofInt n) = (n : ℚ) := by
  change (n.toNat : ℚ) - ((-n).toNat : ℚ) = (n : ℚ)
  exact_mod_cast Int.toNat_sub_toNat_neg n

/-- The product pair has distinct components when both input pairs have distinct components. -/
theorem mul_ne {x y : Pair} (hx : x.1 ≠ x.2) (hy : y.1 ≠ y.2) : (mul x y).1 ≠ (mul x y).2 := by
  intro h
  have he := (value_eq_zero (mul x y)).mpr h
  rw [value_mul] at he
  exact (mul_ne_zero (mt (value_eq_zero x).mp hx) (mt (value_eq_zero y).mp hy)) he

/-- Both natural-number components of a redundant signed pair are at most `2 ^ b`. -/
def Bound (b : ℕ) (x : Pair) : Prop := x.1 ≤ 2 ^ b ∧ x.2 ≤ 2 ^ b

/-- A component size bound for a pair remains valid when its exponent is increased. -/
theorem mono {b c : ℕ} {x : Pair} (hx : Bound b x) (h : b ≤ c) : Bound c x := by
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) h
  exact ⟨hx.1.trans hp, hx.2.trans hp⟩

/-- Exchanging the components of a pair preserves its size bound. -/
theorem neg_bound {b : ℕ} {x : Pair} (h : Bound b x) : Bound b (neg x) := ⟨h.2, h.1⟩

/-- Adding two pairs whose components are bounded by `2 ^ b` gives components bounded by `2 ^ (b
+ 1)`. -/
theorem add_bound {b : ℕ} {x y : Pair} (hx : Bound b x) (hy : Bound b y) : Bound (b + 1) (add x y) := by
  have hp : 2 ^ (b + 1) = 2 ^ b + 2 ^ b := by rw [Nat.pow_succ]; omega
  constructor
  · change x.1 + y.1 ≤ _
    rw [hp]
    exact Nat.add_le_add hx.1 hy.1
  · change x.2 + y.2 ≤ _
    rw [hp]
    exact Nat.add_le_add hx.2 hy.2

/-- Multiplying pairs with size exponents `b` and `c` gives a pair with size exponent `b + c +
1`. -/
theorem mul_bound {b c : ℕ} {x y : Pair} (hx : Bound b x) (hy : Bound c y) : Bound (b + c + 1) (mul x y) := by
  have hp : 2 ^ b * 2 ^ c + 2 ^ b * 2 ^ c = 2 ^ (b + c + 1) := by
    simp only [Nat.pow_add, Nat.pow_one]; ring
  constructor
  · exact (Nat.add_le_add (Nat.mul_le_mul hx.1 hy.1) (Nat.mul_le_mul hx.2 hy.2)).trans_eq hp
  · exact (Nat.add_le_add (Nat.mul_le_mul hx.1 hy.2) (Nat.mul_le_mul hx.2 hy.1)).trans_eq hp

/-- The pair representing an integer satisfies `Bound b` when the integer magnitude is at most
`2 ^ b`. -/
theorem ofInt_bound {b : ℕ} {n : ℤ} (h : n.natAbs ≤ 2 ^ b) : Bound b (ofInt n) := by
  have he := Int.toNat_add_toNat_neg_eq_natAbs n
  constructor <;> dsimp only [ofInt]
  all_goals omega

end Pair

/-- A redundant rational representation with a numerator pair and a denominator pair whose
components are distinct. -/
structure Frac where
  num : Pair
  den : Pair
  den_ne : den.1 ≠ den.2
  deriving DecidableEq

/-- Interpret a redundant fraction as the rational quotient of its numerator and denominator
pair values. -/
def value (x : Frac) : ℚ := Pair.value x.num / Pair.value x.den

/-- Represent a natural number by numerator pair `(n, 0)` and denominator pair `(1, 0)`. -/
def ofNat (n : ℕ) : Frac := ⟨(n, 0), (1, 0), by decide⟩
/-- Represent an integer using `Pair.ofInt` for the numerator and the unit denominator pair. -/
def ofInt (n : ℤ) : Frac := ⟨Pair.ofInt n, (1, 0), by decide⟩
/-- Represent a rational number using its reduced integer numerator and positive natural
denominator as redundant pairs. -/
def ofRat (x : ℚ) : Frac := ⟨Pair.ofInt x.num, (x.den, 0), by have h := x.den_pos; omega⟩
/-- Negate a redundant fraction by exchanging its numerator components and retaining its
denominator. -/
def neg (x : Frac) : Frac := ⟨Pair.neg x.num, x.den, x.den_ne⟩
/-- Multiply redundant fractions by multiplying their numerator pairs and denominator pairs. -/
def mul (x y : Frac) : Frac :=
    ⟨Pair.mul x.num y.num, Pair.mul x.den y.den, Pair.mul_ne x.den_ne y.den_ne⟩
/-- Add redundant fractions using cross-multiplied numerators and the product denominator. -/
def add (x y : Frac) : Frac :=
  ⟨Pair.add (Pair.mul x.num y.den) (Pair.mul y.num x.den), Pair.mul x.den y.den, Pair.mul_ne x.den_ne y.den_ne⟩
/-- Subtract redundant fractions by adding the negation of the second fraction. -/
def sub (x y : Frac) : Frac := add x (neg y)
/-- Return the fixed zero representation when the numerator components are equal; otherwise
exchange the numerator and denominator pairs. -/
def inv (x : Frac) : Frac := if h : x.num.1 = x.num.2 then ofNat 0 else ⟨x.den, x.num, h⟩
/-- Divide redundant fractions by multiplying the first fraction by the total inverse of the
second. -/
def div (x y : Frac) : Frac := mul x (inv y)
/-- Compute a natural power by repeated redundant multiplication, starting with the unit
representation at exponent zero. -/
def pow (x : Frac) : ℕ → Frac | 0 => ofNat 1 | n + 1 => mul (pow x n) x

/-- The denominator pair of a redundant fraction has nonzero rational value. -/
theorem den_value_ne (x : Frac) : Pair.value x.den ≠ 0 := mt (Pair.value_eq_zero x.den).mp x.den_ne

/-- The redundant fraction representing a natural number has the expected rational value. -/
theorem value_ofNat (n : ℕ) : value (ofNat n) = (n : ℚ) := by simp [value, ofNat, Pair.value]

/-- The redundant fraction representing an integer has the expected rational value. -/
theorem value_ofInt (n : ℤ) : value (ofInt n) = (n : ℚ) := by
  change Pair.value (Pair.ofInt n) / Pair.value (1, 0) = _
  rw [Pair.value_ofInt]
  norm_num [Pair.value]

/-- Embedding a rational number as a redundant fraction preserves its value. -/
theorem value_ofRat (x : ℚ) : value (ofRat x) = x := by
  change Pair.value (Pair.ofInt x.num) / Pair.value (x.den, 0) = x
  rw [Pair.value_ofInt]
  simpa only [Pair.value, Nat.cast_zero, sub_zero] using Rat.num_div_den x

/-- Redundant fraction negation negates the interpreted rational value. -/
theorem value_neg (x : Frac) : value (neg x) = -value x := by
    simp only [value, neg, Pair.value_neg, neg_div]

/-- Redundant fraction multiplication multiplies the interpreted rational values. -/
theorem value_mul (x y : Frac) : value (mul x y) = value x * value y := by
  simp only [value, mul, Pair.value_mul]
  ring

/-- Redundant fraction addition adds the interpreted rational values. -/
theorem value_add (x y : Frac) : value (add x y) = value x + value y := by
  simp only [value, add, Pair.value_add, Pair.value_mul]
  field_simp [den_value_ne x, den_value_ne y]

/-- Redundant fraction subtraction subtracts the interpreted rational values. -/
theorem value_sub (x y : Frac) : value (sub x y) = value x - value y := by
  simp only [sub, value_add, value_neg, sub_eq_add_neg]

/-- Total inversion of a redundant fraction gives the inverse of its interpreted rational value,
including at zero. -/
theorem value_inv (x : Frac) : value (inv x) = (value x)⁻¹ := by
  by_cases h : x.num.1 = x.num.2
  · simp [inv, h, value, ofNat, Pair.value]
  · simp [inv, h, value, inv_div]

/-- Redundant fraction division gives the quotient of the interpreted rational values. -/
theorem value_div (x y : Frac) : value (div x y) = value x / value y := by
  simp only [div, value_mul, value_inv, div_eq_mul_inv]

/-- Interpreting a natural power of a redundant fraction gives the corresponding power of its
rational value. -/
theorem value_pow (x : Frac) (n : ℕ) : value (pow x n) = value x ^ n := by
  induction n with
  | zero => simp [pow, value_ofNat]
  | succ n ih => simp only [pow, value_mul, ih, pow_succ]

/-- All components of the numerator and denominator pairs are at most `2 ^ b`. -/
def Bound (b : ℕ) (x : Frac) : Prop := Pair.Bound b x.num ∧ Pair.Bound b x.den

/-- A component size bound for a redundant fraction remains valid when its exponent is
increased. -/
theorem mono {b c : ℕ} {x : Frac} (hx : Bound b x) (h : b ≤ c) : Bound c x :=
  ⟨Pair.mono hx.1 h, Pair.mono hx.2 h⟩

/-- The redundant representation of `n` satisfies the size bound with exponent `b` when `n ≤ 2 ^
b`. -/
theorem ofNat_bound {b n : ℕ} (h : n ≤ 2 ^ b) : Bound b (ofNat n) :=
  ⟨⟨h, Nat.zero_le _⟩, ⟨Nat.one_le_two_pow, Nat.zero_le _⟩⟩

/-- The redundant representation of a natural number `n` satisfies the size bound with exponent
`n`. -/
theorem nat_bound (n : ℕ) : Bound n (ofNat n) := ofNat_bound (Nat.lt_two_pow_self (n := n)).le

/-- The redundant representation of an integer satisfies the size bound with exponent `b` when
its magnitude is at most `2 ^ b`. -/
theorem ofInt_bound {b : ℕ} {n : ℤ} (h : n.natAbs ≤ 2 ^ b) : Bound b (ofInt n) :=
  ⟨Pair.ofInt_bound h, ⟨Nat.one_le_two_pow, Nat.zero_le _⟩⟩

/-- A reduced rational size bound transfers to the same component size bound for its redundant
representation. -/
theorem ofRat_bound {b : ℕ} {x : ℚ} (h : RationalDataSize.Bound b x) : Bound b (ofRat x) :=
  ⟨Pair.ofInt_bound h.1, ⟨h.2, Nat.zero_le _⟩⟩

/-- Negating a redundant fraction preserves its component size bound. -/
theorem neg_bound {b : ℕ} {x : Frac} (h : Bound b x) : Bound b (neg x) := ⟨Pair.neg_bound h.1, h.2⟩

/-- Multiplying redundant fractions with size exponents `b` and `c` gives a bound with exponent
`b + c + 1`. -/
theorem mul_bound {b c : ℕ} {x y : Frac} (hx : Bound b x) (hy : Bound c y) : Bound (b + c + 1) (mul x y) :=
  ⟨Pair.mul_bound hx.1 hy.1, Pair.mul_bound hx.2 hy.2⟩

/-- Adding redundant fractions with size exponents `b` and `c` gives a bound with exponent `b +
c + 2`. -/
theorem add_bound {b c : ℕ} {x y : Frac} (hx : Bound b x) (hy : Bound c y) : Bound (b + c + 2) (add x y) := by
  have hxy := Pair.mul_bound hx.1 hy.2
  have hyx : Pair.Bound (b + c + 1) (Pair.mul y.num x.den) := by
    simpa only [Nat.add_comm c b] using Pair.mul_bound hy.1 hx.2
  exact ⟨Pair.add_bound hxy hyx, Pair.mono (Pair.mul_bound hx.2 hy.2) (by omega)⟩

/-- Subtracting redundant fractions with size exponents `b` and `c` gives a bound with exponent
`b + c + 2`. -/
theorem sub_bound {b c : ℕ} {x y : Frac} (hx : Bound b x) (hy : Bound c y) : Bound (b + c + 2) (sub x y) :=
  add_bound hx (neg_bound hy)

/-- Total inversion of a redundant fraction preserves its component size bound. -/
theorem inv_bound {b : ℕ} {x : Frac} (h : Bound b x) : Bound b (inv x) := by
  unfold inv
  split
  · exact ofNat_bound (Nat.zero_le _)
  · exact ⟨h.2, h.1⟩

/-- Dividing redundant fractions with size exponents `b` and `c` gives a bound with exponent `b
+ c + 1`. -/
theorem div_bound {b c : ℕ} {x y : Frac} (hx : Bound b x) (hy : Bound c y) : Bound (b + c + 1) (div x y) :=
  mul_bound hx (inv_bound hy)

/-- The natural power of a redundant fraction with size exponent `b` has a bound with exponent
`n * (b + 1)`. -/
theorem pow_bound {b : ℕ} {x : Frac} (hx : Bound b x) (n : ℕ) : Bound (n * (b + 1)) (pow x n) := by
  induction n with
  | zero => exact ofNat_bound (by simp)
  | succ n ih =>
    have h := mul_bound ih hx
    convert! h using 1
    ring

end Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine.RedundantRational
