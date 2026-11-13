/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Qatlib.Papers.GrpCommTest05.MainResults.Lemma2Counting
import Qatlib.Papers.GrpCommTest05.MainResults.HammingCoupling

/-!
# Algebraic cost substitutions for group commutativity testing

The complement `1 - pp k l` is rewritten as a rational expression and bounded below by `l/k`
when `2*l ≤ k`. These identities isolate the parameter dependence in the counting estimate.

`query_cost_substitution` rewrites the real square root and logarithmic factors in the query
cost expression under positivity hypotheses. See [MagniezNayak2005].

## Main statements

* `one_sub_pp_ge_l_div_k`: If `k ≥ 2` and `2*l ≤ k`, then `l/k ≤ 1 - pp k l` over the rationals.
* `query_cost_substitution`: For positive `k`, `l`, and `log l`, the expression `(k/l) * sqrt (l
  * log l) * log l` equals `(k / sqrt l) * (log l)^(3/2)`.

## References

* [Magniez and Nayak, 2005][MagniezNayak2005]
-/

set_option autoImplicit false

namespace Qatlib.Papers.GrpCommTest05.MainResults

open Real

/-- For `k ≥ 2`, `1 - pp k l` equals `2*l*(k-l) / (k*(k-1))` over the rationals. See
[MagniezNayak2005]. -/
theorem one_sub_pp_eq {k l : ℕ} (hk : 2 ≤ k) :
    1 - pp k l = (2 * (l : ℚ) * ((k : ℚ) - l)) / ((k : ℚ) * ((k : ℚ) - 1)) := by
  have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hk1 : ((k : ℚ) - 1) ≠ 0 := by
    have : (1 : ℚ) < k := by exact_mod_cast hk
    linarith
  rw [pp]
  field_simp
  ring

/-- If `k ≥ 2` and `2*l ≤ k`, then `l/k ≤ 1 - pp k l` over the rationals. See
[MagniezNayak2005]. -/
theorem one_sub_pp_ge_l_div_k {k l : ℕ} (hk : 2 ≤ k) (hlk2 : 2 * l ≤ k) :
    (l : ℚ) / (k : ℚ) ≤ 1 - pp k l := by
  have hkq : (0 : ℚ) < k := by exact_mod_cast (by omega : 0 < k)
  have hden : (0 : ℚ) < (k : ℚ) * ((k : ℚ) - 1) := by
    apply mul_pos hkq
    have : (1 : ℚ) < k := by exact_mod_cast hk
    linarith
  rw [one_sub_pp_eq hk, div_le_div_iff₀ hkq hden]
  have hlk : (2 : ℚ) * l ≤ k := by exact_mod_cast hlk2
  have hfac : 2 * (l : ℚ) * ((k : ℚ) - l) * (k : ℚ) -
      (l : ℚ) * ((k : ℚ) * ((k : ℚ) - 1)) =
      (l : ℚ) * (k : ℚ) * ((k : ℚ) - 2 * (l : ℚ) + 1) := by ring
  have hnn : 0 ≤ (l : ℚ) * (k : ℚ) * ((k : ℚ) - 2 * (l : ℚ) + 1) := by
    apply mul_nonneg (mul_nonneg (by positivity) hkq.le)
    linarith
  nlinarith [hfac, hnn]

/-- For positive `k`, `l`, and `log l`, the expression `(k/l) * sqrt (l * log l) * log l` equals
`(k / sqrt l) * (log l)^(3/2)`. See [MagniezNayak2005]. -/
theorem query_cost_substitution {k l : ℝ} (hk : 0 < k) (hl : 0 < l)
    (hlog : 0 < Real.log l) :
    (k / l) * Real.sqrt (l * Real.log l) * Real.log l =
      k / Real.sqrt l * (Real.log l) ^ ((3 : ℝ) / 2) := by
  have hsl : Real.sqrt l * Real.sqrt l = l := Real.mul_self_sqrt hl.le
  have hsqlog : Real.sqrt (Real.log l) * Real.sqrt (Real.log l) = Real.log l :=
    Real.mul_self_sqrt hlog.le
  have hsqrt_mul : Real.sqrt (l * Real.log l) =
      Real.sqrt l * Real.sqrt (Real.log l) := Real.sqrt_mul hl.le _
  have hrpow : (Real.log l) ^ ((3 : ℝ) / 2) =
      Real.sqrt (Real.log l) * Real.log l := by
    have hsplit : ((3 : ℝ) / 2) = 1 + 1 / 2 := by norm_num
    rw [hsplit, Real.rpow_add hlog, Real.rpow_one, ← Real.sqrt_eq_rpow]
    ring
  rw [hsqrt_mul, hrpow]
  field_simp
  nlinarith [hsl, hsqlog]

end Qatlib.Papers.GrpCommTest05.MainResults
