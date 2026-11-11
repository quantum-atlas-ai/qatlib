/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.JonesPoly06.MainResults.AmplitudeApprox
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Arithmetic support for oracle error transfer

`decides` expresses correct threshold decisions for probabilities promised to lie below 1/4 or
above 3/4. The module proves error-composition and squaring estimates, bounds normalized Boolean
counts, and controls errors in powers of contractions. See [WocjanYard2006].

## Main statements

* `decides_iff_of_gap`: Under the low-or-high promise and error less than 1/4, the high and low
  cases are respectively equivalent to z ≥ 1/2 and z < 1/2.
* `pow_error_of_div`: For a positive exponent e and nonnegative ε, two contractions within ε/e
  have e-th powers within ε.

## References

* [Wocjan and Yard, 2006][WocjanYard2006]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.JonesPoly06.MainResults

/-- The threshold correctness condition that p ≥ 3/4 forces z ≥ 1/2 and p ≤ 1/4 forces z < 1/2. -/
def decides (z p : ℝ) : Prop :=
  (3 / 4 ≤ p → 1 / 2 ≤ z) ∧ (p ≤ 1 / 4 → z < 1 / 2)

/-- An estimate with absolute error less than 1/4 satisfies `decides`; see [WocjanYard2006]. -/
theorem decides_of_error {z p : ℝ} (h : |z - p| < 1 / 4) : decides z p := by
  rw [abs_lt] at h
  obtain ⟨h1, h2⟩ := h
  exact ⟨fun hp => by linarith, fun hp => by linarith⟩

/-- Under the low-or-high promise and error less than 1/4, the high and low cases are
respectively equivalent to z ≥ 1/2 and z < 1/2; see [WocjanYard2006]. -/
theorem decides_iff_of_gap {z p : ℝ} (hg : p ≤ 1 / 4 ∨ 3 / 4 ≤ p)
    (h : |z - p| < 1 / 4) :
    (3 / 4 ≤ p ↔ 1 / 2 ≤ z) ∧ (p ≤ 1 / 4 ↔ z < 1 / 2) := by
  rw [abs_lt] at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · constructor
    · intro hp; linarith
    · intro hz
      by_contra h3
      have h3' : p < 3 / 4 := not_le.mp h3
      rcases hg with hp | hp <;> linarith
  · constructor
    · intro hp; linarith
    · intro hz
      rcases hg with hp | hp
      · exact hp
      · exfalso; linarith

/-- Two successive absolute-error bounds x and y give a total absolute-error bound x + y. -/
theorem abs_sub_le_add_of_abs {a b c x y : ℝ} (h1 : |a - b| ≤ x)
    (h2 : |b - c| ≤ y) : |a - c| ≤ x + y := by
  calc |a - c| = |(a - b) + (b - c)| := by
        rw [show (a - b) + (b - c) = a - c by ring]
    _ ≤ |a - b| + |b - c| := abs_add_le _ _
    _ ≤ x + y := add_le_add h1 h2

/-- For a and b in [0, 1], the absolute difference of their squares is at most twice their
absolute difference; see [WocjanYard2006]. -/
theorem sq_sub_sq_le_two_mul {a b : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha1 : a ≤ 1) (hb1 : b ≤ 1) : |a ^ 2 - b ^ 2| ≤ 2 * |a - b| := by
  have h : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
  rw [h, abs_mul]
  have hsum : |a + b| ≤ 2 := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  calc |a - b| * |a + b| ≤ |a - b| * 2 :=
        mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ = 2 * |a - b| := by ring

/-- For nonnegative a and b, the square of their absolute difference is at most the absolute
difference of their squares; see [WocjanYard2006]. -/
theorem abs_sub_sq_le_abs_sq_sub_sq {a b : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) :
    |a - b| ^ 2 ≤ |a ^ 2 - b ^ 2| := by
  have h : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
  rw [h, abs_mul, pow_two]
  have hab : |a + b| = a + b := abs_of_nonneg (by linarith)
  have hsum : |a - b| ≤ |a + b| := by
    rw [hab]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  exact mul_le_mul_of_nonneg_left hsum (abs_nonneg _)

/-- If Z and s lie in [0, 1], |Z − s| < 1/16, and |s² − p| ≤ 1/16, then |Z² − p| < 1/4; see
[WocjanYard2006]. -/
theorem amplitude_sq_chain {Z s p : ℝ} (hZ0 : 0 ≤ Z) (hZ1 : Z ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hZ : |Z - s| < 1 / 16)
    (hp : |s ^ 2 - p| ≤ 1 / 16) : |Z ^ 2 - p| < 1 / 4 := by
  have h1 : |Z ^ 2 - s ^ 2| ≤ 2 * |Z - s| := sq_sub_sq_le_two_mul hZ0 hs0 hZ1 hs1
  have h2 : 2 * |Z - s| < 1 / 8 := by linarith
  have h3 : |Z ^ 2 - s ^ 2| < 1 / 8 := lt_of_le_of_lt h1 h2
  have h4 : |Z ^ 2 - p| ≤ |Z ^ 2 - s ^ 2| + |s ^ 2 - p| :=
    abs_sub_le_add_of_abs le_rfl le_rfl
  linarith

/-- The real-valued count of Boolean inputs on which f is true. -/
def countTrue {n : ℕ} (f : (Fin n → Bool) → Bool) : ℝ :=
  ∑ x : Fin n → Bool, if f x then (1 : ℝ) else 0

/-- The number `countTrue f` is nonnegative. -/
theorem countTrue_nonneg {n : ℕ} (f : (Fin n → Bool) → Bool) :
    0 ≤ countTrue f := by
  unfold countTrue
  exact Finset.sum_nonneg (fun x _ => by by_cases h : f x <;> simp [h])

/-- A Boolean function on n bits is true on at most 2^n inputs. -/
theorem countTrue_le_pow {n : ℕ} (f : (Fin n → Bool) → Bool) :
    countTrue f ≤ (2 : ℝ) ^ n := by
  unfold countTrue
  have h1 : (∑ x : Fin n → Bool, (if f x then (1 : ℝ) else 0))
      ≤ ∑ _x : Fin n → Bool, (1 : ℝ) := by
    refine Finset.sum_le_sum (fun x _ => ?_)
    by_cases h : f x <;> simp [h]
  have h2 : (∑ _x : Fin n → Bool, (1 : ℝ)) = (Fintype.card (Fin n → Bool) : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have h3 : (Fintype.card (Fin n → Bool) : ℝ) = (2 : ℝ) ^ n := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    push_cast
    ring
  linarith

/-- The fraction `countTrue f / 2^n` lies in [0, 1]; see [WocjanYard2006]. -/
theorem countTrue_normalized_mem {n : ℕ} (f : (Fin n → Bool) → Bool) :
    countTrue f / (2 : ℝ) ^ n ∈ Set.Icc (0 : ℝ) 1 := by
  have hn : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  constructor
  · exact div_nonneg (countTrue_nonneg f) hn.le
  · rw [div_le_one hn]
    exact countTrue_le_pow f

/-- If W² = 1 in a monoid, conjugation by W carries a product to the product of the conjugates. -/
theorem conj_mul {M : Type*} [Monoid M] (W U V : M) (hW : W * W = 1) :
    (W * U * W) * (W * V * W) = W * (U * V) * W := by
  calc (W * U * W) * (W * V * W)
      = W * U * (W * W) * V * W := by simp only [mul_assoc]
    _ = W * U * 1 * V * W := by rw [hW]
    _ = W * (U * V) * W := by simp only [mul_assoc, mul_one]

/-- If W² = 1, the e-th power of WUW equals WU^eW; see [WocjanYard2006]. -/
theorem conj_pow {M : Type*} [Monoid M] (W U : M) (hW : W * W = 1) (e : ℕ) :
    (W * U * W) ^ e = W * U ^ e * W := by
  induction e with
  | zero => simp [hW]
  | succ e ih =>
      rw [pow_succ, ih, pow_succ]
      exact conj_mul W (U ^ e) U hW

/-- For a positive exponent e and nonnegative ε, two contractions within ε/e have e-th powers
within ε; see [WocjanYard2006]. -/
theorem pow_error_of_div {A : Type*} [SeminormedRing A] [NormOneClass A]
    (a b : A) (e : ℕ) (he : 0 < e) (ε : ℝ) (hε : 0 ≤ ε)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (h : ‖a - b‖ ≤ ε / e) :
    ‖a ^ e - b ^ e‖ ≤ ε := by
  have hbnd := pow_sub_pow_le a b ha hb e
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have hstep : (e : ℝ) * ‖a - b‖ ≤ (e : ℝ) * (ε / e) :=
    mul_le_mul_of_nonneg_left h heR.le
  have heq : (e : ℝ) * (ε / e) = ε := by field_simp
  linarith [hbnd, hstep]

end Qatlib.Papers.JonesPoly06.MainResults
