/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Size bounds for rational data

`RationalDataSize.Bound b x` bounds both the absolute numerator and the denominator of a reduced
rational by `2 ^ b`. The module relates this bound to a binary span and propagates it through
rational arithmetic, with additive exponent bounds for multiplication and division and one extra
exponent unit for addition and subtraction.

For background on classical computation and its resource models, see [KitaevShenVyalyi2002].

## Main statements

* `span_le`: bounds the binary span from a numerator-denominator bound.
* `fraction`: transfers a bound from an unreduced fraction.
* `mul`, `add`, `div`, and `pow`: size propagation through arithmetic.

## References

* [Kitaev, Shen and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option autoImplicit false
namespace Qatlib.Concepts.FinitePrecision.ComputableInput.RationalDataSize

/-- Both the natural absolute numerator and the denominator of `x` are at most `2 ^ b`. -/
def Bound (b : ℕ) (x : ℚ) : Prop := x.num.natAbs ≤ 2 ^ b ∧ x.den ≤ 2 ^ b

/-- One plus the sum of the base-two ceiling logarithms of the absolute numerator plus one and
denominator plus one. -/
def binarySpan (x : ℚ) : ℕ := 1 + Nat.clog 2 (x.num.natAbs + 1) + Nat.clog 2 (x.den + 1)

/-- A rational satisfying `Bound b` has binary span at most `2 * b + 3`. -/
theorem span_le {b : ℕ} {x : ℚ} (h : Bound b x) : binarySpan x ≤ 2 * b + 3 := by
  obtain ⟨hnum, hden⟩ := h
  have hp : 1 ≤ 2 ^ b := Nat.two_pow_pos b
  have hn : x.num.natAbs + 1 ≤ 2 ^ (b + 1) := by rw [pow_succ]; omega
  have hd : x.den + 1 ≤ 2 ^ (b + 1) := by rw [pow_succ]; omega
  have h1 := Nat.clog_le_of_le_pow hn
  have h2 := Nat.clog_le_of_le_pow hd
  unfold binarySpan
  omega

/-- A rational size bound remains valid when its exponent parameter is increased. -/
theorem mono {b c : ℕ} {x : ℚ} (h : Bound b x) (hbc : b ≤ c) : Bound c x := by
  have hp : 2 ^ b ≤ 2 ^ c := Nat.pow_le_pow_right (by decide) hbc
  exact ⟨h.1.trans hp, h.2.trans hp⟩

/-- A fraction with positive denominator satisfies `Bound b` when its unreduced numerator
magnitude and denominator are both at most `2 ^ b`. -/
theorem fraction {b : ℕ} (n : ℤ) (d : ℕ) (hd : 0 < d)
    (hn : n.natAbs ≤ 2 ^ b) (hden : d ≤ 2 ^ b) : Bound b ((n : ℚ) / d) := by
  have he : (n : ℚ) / d = Rat.divInt n (d : ℤ) := by rw [Rat.divInt_eq_div]; rfl
  rw [he]
  constructor
  · by_cases hz : n = 0
    · simp [hz]
    · exact (Nat.le_of_dvd (Int.natAbs_pos.mpr hz)
        (Int.natAbs_dvd_natAbs.mpr (Rat.num_dvd n (by exact_mod_cast hd.ne')))).trans hn
  · have hh := Rat.den_dvd n (d : ℤ)
    have hdiv : (Rat.divInt n (d : ℤ)).den ∣ d := Int.natCast_dvd_natCast.mp hh
    exact (Nat.le_of_dvd hd hdiv).trans hden

/-- The rational zero satisfies `Bound 0`. -/
theorem zero : Bound 0 0 := by unfold Bound; decide +kernel

/-- The rational one satisfies `Bound 0`. -/
theorem one : Bound 0 1 := by unfold Bound; decide +kernel

/-- The rational cast of a natural `n` satisfies `Bound n`. -/
theorem natCast (n : ℕ) : Bound n (n : ℚ) := by
  constructor
  · simpa using (Nat.lt_two_pow_self (n := n)).le
  · change 1 ≤ 2 ^ n
    exact Nat.one_le_two_pow

/-- The rational cast of an integer `n` satisfies `Bound n.natAbs`. -/
theorem intCast (n : ℤ) : Bound n.natAbs (n : ℚ) := by
  constructor
  · simpa using (Nat.lt_two_pow_self (n := n.natAbs)).le
  · change 1 ≤ 2 ^ n.natAbs
    exact Nat.one_le_two_pow

/-- Negation preserves a rational numerator-denominator bound. -/
theorem neg {b : ℕ} {x : ℚ} (h : Bound b x) : Bound b (-x) := by
  simpa only [Bound, Rat.neg_num, Rat.neg_den, Int.natAbs_neg] using h

/-- Inversion preserves a rational numerator-denominator bound, including the zero case. -/
theorem inv {b : ℕ} {x : ℚ} (h : Bound b x) : Bound b x⁻¹ := by
  constructor
  · simp only [Rat.num_inv, Int.natAbs_mul, Int.natAbs_natCast]
    have hs : x.num.sign.natAbs ≤ 1 := by rw [Int.natAbs_sign]; split_ifs <;> omega
    exact (Nat.mul_le_mul_right x.den hs).trans (by simpa using h.2)
  · rw [Rat.den_inv]
    split_ifs
    · exact le_trans (by decide : 1 ≤ 2 ^ 0) (Nat.pow_le_pow_right (by decide) (Nat.zero_le b))
    · exact h.1

/-- Multiplying rationals bounded by exponents `b` and `c` gives a rational bounded by exponent
`b + c`. -/
theorem mul {b c : ℕ} {x y : ℚ} (hx : Bound b x) (hy : Bound c y) : Bound (b + c) (x * y) := by
  have he : x * y = ((x.num * y.num : ℤ) : ℚ) / (x.den * y.den : ℕ) := by
    calc
      x * y = ((x.num : ℚ) / x.den) * ((y.num : ℚ) / y.den) := by rw [Rat.num_div_den, Rat.num_div_den]
      _ = _ := by push_cast; ring
  rw [he]
  apply fraction _ _ (Nat.mul_pos x.pos y.pos)
  · rw [Int.natAbs_mul, pow_add]
    exact Nat.mul_le_mul hx.1 hy.1
  · rw [pow_add]
    exact Nat.mul_le_mul hx.2 hy.2

/-- Adding rationals bounded by exponents `b` and `c` gives a rational bounded by exponent `b +
c + 1`. -/
theorem add {b c : ℕ} {x y : ℚ} (hx : Bound b x) (hy : Bound c y) : Bound (b + c + 1) (x + y) := by
  have he : x + y = ((x.num * y.den + y.num * x.den : ℤ) : ℚ) / (x.den * y.den : ℕ) := by
    have hxd : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_nz
    have hyd : (y.den : ℚ) ≠ 0 := by exact_mod_cast y.den_nz
    calc
      x + y = (x.num : ℚ) / x.den + (y.num : ℚ) / y.den := by rw [Rat.num_div_den, Rat.num_div_den]
      _ = _ := by push_cast; field_simp [hxd, hyd]
  rw [he]
  apply fraction _ _ (Nat.mul_pos x.pos y.pos)
  · calc
      _ ≤ (x.num * y.den : ℤ).natAbs + (y.num * x.den : ℤ).natAbs := Int.natAbs_add_le _ _
      _ = x.num.natAbs * y.den + y.num.natAbs * x.den := by simp only [Int.natAbs_mul, Int.natAbs_natCast]
      _ ≤ 2 ^ b * 2 ^ c + 2 ^ c * 2 ^ b := Nat.add_le_add (Nat.mul_le_mul hx.1 hy.2) (Nat.mul_le_mul hy.1 hx.2)
      _ = 2 ^ (b + c + 1) := by rw [pow_succ, pow_add]; ring
  · have hm := Nat.mul_le_mul hx.2 hy.2
    rw [pow_succ, pow_add]
    omega

/-- Subtracting rationals bounded by exponents `b` and `c` gives a rational bounded by exponent
`b + c + 1`. -/
theorem sub {b c : ℕ} {x y : ℚ} (hx : Bound b x) (hy : Bound c y) : Bound (b + c + 1) (x - y) := by
  simpa only [sub_eq_add_neg] using add hx (neg hy)

/-- Dividing rationals bounded by exponents `b` and `c` gives a rational bounded by exponent `b
+ c`. -/
theorem div {b c : ℕ} {x y : ℚ} (hx : Bound b x) (hy : Bound c y) : Bound (b + c) (x / y) := by
  simpa only [div_eq_mul_inv] using mul hx (inv hy)

/-- The `n`th power of a rational satisfying `Bound b` satisfies `Bound (n * b)`. -/
theorem pow {b : ℕ} {x : ℚ} (h : Bound b x) (n : ℕ) : Bound (n * b) (x ^ n) := by
  induction n with
  | zero => simpa using one
  | succ n ih => simpa only [Nat.succ_mul, pow_succ] using mul ih h

end Qatlib.Concepts.FinitePrecision.ComputableInput.RationalDataSize
