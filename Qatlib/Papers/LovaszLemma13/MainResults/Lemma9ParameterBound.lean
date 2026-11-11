/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 9 of arXiv:1311.6474v1

Source: Martin Schwarz, Toby S. Cubitt, Frank Verstraete,
*An Information-Theoretic Proof of the Constructive Commutative Quantum Lovász Local Lemma*,
arXiv:1311.6474v1, Lemma 9 and Eq. (59)–(66) (Appendix A.2, p. 14).

The parameter `N` of the algorithm is defined implicitly by

  `N = log(N) / (k - log(der)) + (m + log(1/ε)) / (k - log(der))`,

i.e. `N = a log N + b` with `a = (k - log(der))⁻¹` and `b = (m + log(1/ε)) / (k - log(der))`.
With `N = t + a log t` the paper derives the explicit upper bound of Eq. (60):

  `N ≤ b + a (log(a+1) + log(b + a log(a+1))) ≤ b + 3 a (log b + 1)`.

All logarithms have base 2, matching the paper.

The first inequality is proved in `lemma9_implicit_bound` from the implicit definition, using
only `log x ≤ x` (proved here as `logb_two_le_self`).  For the second (relaxed) inequality the
paper only uses it in its own parameter regime; the statement is *not* valid for arbitrary
`a, b ≥ 0` (already `a = 2, b = 1` violates it), so `lemma9_explicit_bound` records the
relaxation under the regime hypotheses `1 ≤ a ≤ b` that hold in the algorithm when
`m ≥ 1`, `ε ≤ 1` and `k - log(der) ≤ 1`.
-/

namespace Qatlib.Papers.LovaszLemma13.MainResults

open scoped BigOperators

set_option autoImplicit false

/-! ## Elementary bounds on logarithms -/

/-- `n + 1 ≤ 2 ^ n` for natural numbers. -/
lemma nat_add_one_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega

/-- `x ≤ 2 ^ x` for nonnegative reals.  On `[0, 1]` this follows from `2 ^ x ≥ 1`; for `x ≥ 1`
it follows from the floor `n = ⌊x⌋` together with `n + 1 ≤ 2 ^ n`. -/
lemma le_two_rpow (x : ℝ) (hx : 0 ≤ x) : x ≤ (2 : ℝ) ^ x := by
  rcases lt_or_ge x 1 with h | h
  · have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ x := Real.one_le_rpow (by norm_num) hx
    linarith
  · set n : ℕ := ⌊x⌋₊ with hn
    have hxn : (n : ℝ) ≤ x := Nat.floor_le hx
    have hlt : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
    have hnat : (n : ℝ) + 1 ≤ (2 : ℝ) ^ n := by
      have := nat_add_one_le_two_pow n
      exact_mod_cast this
    have hmono : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ x := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hxn
      simpa [Real.rpow_natCast] using h
    linarith

/-- `log₂ x ≤ x` for nonnegative reals; this is the only analytic input of Lemma 9. -/
lemma logb_two_le_self (x : ℝ) (hx : 0 ≤ x) : Real.logb 2 x ≤ x := by
  rcases eq_or_lt_of_le hx with h | h
  · subst h
    simp
  · rw [Real.logb_le_iff_le_rpow (by norm_num) h]
    exact le_two_rpow x hx

/-! ## The implicit bound -/

/-- **Lemma 9, first inequality of Eq. (60).**  Let `a, b ≥ 0` and let `N > 0` satisfy the
implicit equation `N = a log₂ N + b` and the substitution `N = t + a log₂ t` with `t > 0`.  Then

  `N ≤ b + a (log₂ (a+1) + log₂ (b + a log₂ (a+1)))`.

This is the paper's derivation (61)–(65): `t + a log t = a log N + b ≤ a log(t(a+1)) + b` using
`log₂ x ≤ x`, which gives `t ≤ a log(a+1) + b`, and monotonicity of `log₂` then bounds
`log t ≤ log(b + a log(a+1))`. -/
theorem lemma9_implicit_bound (a b t N : ℝ) (ha : 0 ≤ a) (ht : 0 < t)
    (hNpos : 0 < N) (hN₁ : N = t + a * Real.logb 2 t) (hN₂ : N = a * Real.logb 2 N + b) :
    N ≤ b + a * (Real.logb 2 (a + 1) + Real.logb 2 (b + a * Real.logb 2 (a + 1))) := by
  have hlogt : Real.logb 2 t ≤ t := logb_two_le_self t (le_of_lt ht)
  have hone : (0 : ℝ) < a + 1 := by linarith
  -- Step 1 (Eq. (62)–(64)): `N ≤ t * (a + 1)`.
  have hNle : N ≤ t * (a + 1) := by nlinarith [hN₁, hlogt]
  -- Step 2: monotonicity of `log₂` gives `log N ≤ log (t (a+1))`.
  have hlogN : Real.logb 2 N ≤ Real.logb 2 (t * (a + 1)) :=
    Real.logb_le_logb_of_le (by norm_num) hNpos hNle
  have hmul : Real.logb 2 (t * (a + 1)) = Real.logb 2 t + Real.logb 2 (a + 1) :=
    Real.logb_mul (ne_of_gt ht) (ne_of_gt hone)
  -- Step 3 (Eq. (64)): `t ≤ a log(a+1) + b`.
  have htle : t ≤ a * Real.logb 2 (a + 1) + b := by
    have hstep : a * Real.logb 2 N + b ≤ a * (Real.logb 2 t + Real.logb 2 (a + 1)) + b := by
      have h := mul_le_mul_of_nonneg_left hlogN ha
      rw [hmul] at h
      linarith
    nlinarith [hstep, hN₁, hN₂]
  -- Step 4 (Eq. (65)): monotonicity of `log₂` applied to `t`.
  have htle' : t ≤ b + a * Real.logb 2 (a + 1) := by linarith
  have hlogtle : Real.logb 2 t ≤ Real.logb 2 (b + a * Real.logb 2 (a + 1)) :=
    Real.logb_le_logb_of_le (by norm_num) ht htle'
  nlinarith [hN₁, htle, hlogtle, ha]

/-- **Lemma 9, second inequality of Eq. (60)**, under the paper's parameter regime `1 ≤ a ≤ b`.

Writing `L = log₂ b ≥ 0`, the two logarithmic terms are bounded by `log₂ (a+1) ≤ L + 1` (since
`a + 1 ≤ 2a ≤ 2b`) and `log₂ (b + a log₂ (a+1)) ≤ log₂ (b (L+2)) = L + log₂ (L+2) ≤ 2L + 2`
(since `log₂ x ≤ x`).  Summing gives `3L + 3`, hence the bound after multiplying by `a`.

Without `a ≤ b` the inequality is false: `a = 2`, `b = 1` gives `1 + 2(log₂ 3 + log₂(1 + 2 log₂ 3))
≈ 8.29 > 7 = 1 + 3·2(log₂ 1 + 1)`. -/
theorem lemma9_explicit_bound (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    b + a * (Real.logb 2 (a + 1) + Real.logb 2 (b + a * Real.logb 2 (a + 1)))
      ≤ b + 3 * a * (Real.logb 2 b + 1) := by
  have ha0 : (0 : ℝ) < a := by linarith
  have hb0 : (0 : ℝ) < b := lt_of_lt_of_le ha0 hab
  have hb1 : (1 : ℝ) ≤ b := le_trans ha hab
  have hlogb : 0 ≤ Real.logb 2 b := Real.logb_nonneg (by norm_num) hb1
  -- `log₂ (a+1) ≤ log₂ (2b) = log₂ b + 1`.
  have hlog1 : Real.logb 2 (a + 1) ≤ Real.logb 2 b + 1 := by
    have h2b : (0 : ℝ) < 2 * b := by linarith
    have hle : a + 1 ≤ 2 * b := by linarith
    have h1 : Real.logb 2 (a + 1) ≤ Real.logb 2 (2 * b) :=
      Real.logb_le_logb_of_le (by norm_num) (by linarith) hle
    have h2 : Real.logb 2 (2 * b) = Real.logb 2 2 + Real.logb 2 b :=
      Real.logb_mul (by norm_num) (ne_of_gt hb0)
    rw [h2] at h1
    norm_num at h1
    linarith [h1]
  -- `b + a log₂ (a+1) ≤ b (log₂ b + 2)`.
  have hargle : b + a * Real.logb 2 (a + 1) ≤ b * (Real.logb 2 b + 2) := by
    have h1 : a * Real.logb 2 (a + 1) ≤ b * (Real.logb 2 b + 1) := by
      have hpos : 0 ≤ Real.logb 2 b + 1 := by linarith
      calc a * Real.logb 2 (a + 1) ≤ a * (Real.logb 2 b + 1) :=
            mul_le_mul_of_nonneg_left hlog1 (le_of_lt ha0)
        _ ≤ b * (Real.logb 2 b + 1) := mul_le_mul_of_nonneg_right hab hpos
    nlinarith [h1]
  have hargpos : 0 < b + a * Real.logb 2 (a + 1) := by
    have : 0 ≤ Real.logb 2 (a + 1) := Real.logb_nonneg (by norm_num) (by linarith)
    nlinarith [mul_nonneg (le_of_lt ha0) this]
  -- `log₂ (b + a log₂ (a+1)) ≤ log₂ (b (log₂ b + 2)) = log₂ b + log₂ (log₂ b + 2)`.
  have hlog2 : Real.logb 2 (b + a * Real.logb 2 (a + 1))
      ≤ 2 * Real.logb 2 b + 2 := by
    have h1 : Real.logb 2 (b + a * Real.logb 2 (a + 1))
        ≤ Real.logb 2 (b * (Real.logb 2 b + 2)) :=
      Real.logb_le_logb_of_le (by norm_num) hargpos hargle
    have h2 : Real.logb 2 (b * (Real.logb 2 b + 2))
        = Real.logb 2 b + Real.logb 2 (Real.logb 2 b + 2) :=
      Real.logb_mul (ne_of_gt hb0) (by linarith)
    have h3 : Real.logb 2 (Real.logb 2 b + 2) ≤ Real.logb 2 b + 2 :=
      logb_two_le_self _ (by linarith)
    linarith [h1, h2.symm ▸ h1, h3]
  have hlog1' : 0 ≤ Real.logb 2 (a + 1) := Real.logb_nonneg (by norm_num) (by linarith)
  nlinarith [hlog1, hlog2, ha0, hlogb, mul_le_mul_of_nonneg_left hlog2 (le_of_lt ha0)]

end Qatlib.Papers.LovaszLemma13.MainResults
