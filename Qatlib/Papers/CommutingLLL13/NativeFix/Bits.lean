/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Binary-logarithm parameters and count support

This module defines the base-two logarithm versions of the slack, reciprocal slack parameter,
and literal ceiling threshold in [SattathArad2015]. It proves positivity of the slack from the
stated local-lemma condition and of `etaBits` from a positive target and slack.

The finite count type `Fin (T + 1)` has `T + 1` elements. `support_log_distinction` records the
difference between the logarithm of this support size and the logarithm of `T` at `T = 1`.

## Main statements

* `slackBits_pos`: The local-lemma inequality gives positive binary-logarithm slack.
* `failureCount_card`: The failure-count index type has `T + 1` elements.
* `support_log_distinction`: The support-size logarithm is `1` at `T = 1`, whereas `logBits 1 =
  0`.

## References

* [Sattath and Arad, 2015][SattathArad2015]
-/

set_option autoImplicit false
namespace Qatlib.Papers.CommutingLLL13.NativeFix
noncomputable section

/-- The base-two logarithm `Real.logb 2 x`. -/
def logBits (x : ℝ) : ℝ := Real.logb 2 x

/-- The binary-logarithm slack `k - logBits(g * r * exp 1)`. -/
def slackBits (k : ℕ) (g r : ℝ) : ℝ := k - logBits (g * r * Real.exp 1)

/-- The reciprocal target-times-slack parameter `1 / (δ * slackBits k g r)`. -/
def etaBits (δ : ℝ) (k : ℕ) (g r : ℝ) : ℝ := 1 / (δ * slackBits k g r)

/-- The natural-number ceiling of `4 * m * η * logBits(η + 2)`. -/
def thresholdBits (m : ℕ) (η : ℝ) : ℕ := Nat.ceil (4 * (m : ℝ) * η * logBits (η + 2))

/-- For positive `g` and `r`, the inequality `g < 2 ^ k / (r * exp 1)` makes the
binary-logarithm slack positive. This is the parameter condition associated with
[SattathArad2015]. -/
theorem slackBits_pos (k : ℕ) (g r : ℝ) (hg : 0 < g) (hr : 0 < r)
    (h : g < (2 : ℝ) ^ (k : ℝ) / (r * Real.exp 1)) :
    0 < slackBits k g r := by
  have hx : 0 < g * r * Real.exp 1 := by positivity
  have hpow : g * r * Real.exp 1 < (2 : ℝ) ^ (k : ℝ) := by
    have h' := (lt_div_iff₀ (show 0 < r * Real.exp 1 by positivity)).mp h
    nlinarith
  exact sub_pos.mpr ((Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 2) hx).mpr hpow)

/-- The parameter `etaBits δ k g r` is positive when `δ` and `slackBits k g r` are positive. -/
theorem etaBits_pos (δ : ℝ) (k : ℕ) (g r : ℝ) (hδ : 0 < δ)
    (hs : 0 < slackBits k g r) : 0 < etaBits δ k g r := by
  exact one_div_pos.mpr (mul_pos hδ hs)

/-- The failure-count index type `Fin (T + 1)` has exactly `T + 1` elements. This is the
count-support size used in the analysis of [SattathArad2015]. -/
theorem failureCount_card (T : ℕ) : Fintype.card (Fin (T + 1)) = T + 1 := Fintype.card_fin _

/-- The binary logarithm of the cardinality of `Fin (1 + 1)` is `1`, whereas `logBits 1 = 0`.
This illustrates the failure-count support-size distinction in the analysis of
[SattathArad2015]. -/
theorem support_log_distinction :
    logBits (Fintype.card (Fin (1 + 1))) = 1 ∧ logBits 1 = 0 := by
  norm_num [logBits, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), Real.logb_one]

end
end Qatlib.Papers.CommutingLLL13.NativeFix
