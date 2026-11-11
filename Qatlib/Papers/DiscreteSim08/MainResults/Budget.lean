/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DiscreteSim08.MainResults.ErrorCorrection
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Arithmetic budgets for discrete query simulation

The expected-query expression `theorem1ExpectedQueries` is bounded using an overhead factor at
most two. Algebraic and logarithmic comparisons then convert truncation-parameter bounds into
explicit query budgets and simplify the known-unitary cost model.

This development follows [CleveEtAl2009].

## Main statements

* `theorem1_query_budget`: the logarithmic truncation bound yields an explicit query budget.
* `main_result_query_log_bound`: replacing `T` by `3 * T` costs at most a factor two in the
  logarithmic ratio.
* `knownUnitary_budget_le`: a bound on `k` controls the known-unitary expression.

## References

* [Cleve et al., 2009][CleveEtAl2009]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.DiscreteSim08.MainResults

/-- The expected-query cost expression `4 * T * A * k`. See [CleveEtAl2009]. -/
noncomputable def theorem1ExpectedQueries (T A k : ℝ) : ℝ := 4 * T * A * k

/-- For nonnegative `T` and `k` and overhead `A ≤ 2`, the expected-query expression is at most
`8 * T * k`. See [CleveEtAl2009]. -/
theorem theorem1ExpectedQueries_le (T A k : ℝ) (hT : 0 ≤ T) (hA : A ≤ 2) (hk : 0 ≤ k) :
    theorem1ExpectedQueries T A k ≤ 8 * T * k := by
  unfold theorem1ExpectedQueries
  nlinarith [mul_nonneg hT hk]

/-- For positive `T`, `ε`, `L`, and `LL`, the bound `k ≤ 2 * L / LL` implies `8 * T * k / ε ≤ 16
* (T * L) / (ε * LL)`. See [CleveEtAl2009]. -/
theorem theorem1_query_budget_arithmetic (T ε k L LL : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (hL : 0 < L) (hLL : 0 < LL) (hkL : k ≤ 2 * L / LL) :
    8 * T * k / ε ≤ 16 * (T * L) / (ε * LL) := by
  have hfac : 0 ≤ 8 * T / ε := by positivity
  have h1 : 8 * T * k / ε = (8 * T / ε) * k := by ring
  have h2 : 16 * (T * L) / (ε * LL) = (8 * T / ε) * (2 * L / LL) := by
    have hε' : ε ≠ 0 := ne_of_gt hε
    have hLL' : LL ≠ 0 := ne_of_gt hLL
    field_simp
    ring
  rw [h1, h2]
  exact mul_le_mul_of_nonneg_left hkL hfac

/-- For positive `T` and `ε` with `1 < log (T / ε)`, the stated logarithmic bound on `k` gives
the query budget `16 * T * log (T / ε) / (ε * log (log (T / ε)))`. See [CleveEtAl2009]. -/
theorem theorem1_query_budget (T ε k : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (h1 : 1 < Real.log (T / ε))
    (hkL : k ≤ 2 * Real.log (T / ε) / Real.log (Real.log (T / ε))) :
    8 * T * k / ε ≤
      16 * (T * Real.log (T / ε)) / (ε * Real.log (Real.log (T / ε))) :=
  theorem1_query_budget_arithmetic T ε k (Real.log (T / ε)) (Real.log (Real.log (T / ε)))
    hT hε (by linarith) (Real.log_pos h1) hkL

/-- For `T > exp 2`, the ratio `log (3 * T) / log (log (3 * T))` is at most twice `log T / log
(log T)`. See [CleveEtAl2009]. -/
theorem main_result_query_log_bound (T : ℝ) (hT : Real.exp 2 < T) :
    Real.log (3 * T) / Real.log (Real.log (3 * T)) ≤
      2 * (Real.log T / Real.log (Real.log T)) := by
  have hTpos : 0 < T := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hTne : T ≠ 0 := ne_of_gt hTpos
  have hlog3T : Real.log (3 * T) = Real.log 3 + Real.log T :=
    Real.log_mul (by norm_num) hTne
  have hT3 : (3 : ℝ) ≤ T := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hlog3_le : Real.log 3 ≤ Real.log T := Real.log_le_log (by norm_num) hT3
  have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlogT_gt2 : 2 < Real.log T := by
    have h := Real.log_lt_log (Real.exp_pos 2) hT
    rwa [Real.log_exp] at h
  have hlogT_pos : 0 < Real.log T := by linarith
  have hA_ge : Real.log T ≤ Real.log (3 * T) := by rw [hlog3T]; linarith
  have hA_le : Real.log (3 * T) ≤ 2 * Real.log T := by rw [hlog3T]; linarith
  have hLB_pos : 0 < Real.log (Real.log T) := Real.log_pos (by linarith)
  have hLA_ge : Real.log (Real.log T) ≤ Real.log (Real.log (3 * T)) :=
    Real.log_le_log hlogT_pos hA_ge
  have hLA_pos : 0 < Real.log (Real.log (3 * T)) := lt_of_lt_of_le hLB_pos hLA_ge
  calc Real.log (3 * T) / Real.log (Real.log (3 * T))
      ≤ (2 * Real.log T) / Real.log (Real.log (3 * T)) :=
        div_le_div_of_nonneg_right hA_le hLA_pos.le
    _ ≤ (2 * Real.log T) / Real.log (Real.log T) :=
        div_le_div_of_nonneg_left (by positivity) hLB_pos hLA_ge
    _ = 2 * (Real.log T / Real.log (Real.log T)) := by ring

/-- For nonnegative `C`, replacing `k ≤ log T` in the known-unitary expression gives `C * T ^ 2
* k ≤ C * T ^ 2 * log T`. See [CleveEtAl2009]. -/
theorem knownUnitary_budget_le (C k T : ℝ) (hC : 0 ≤ C) (hk : k ≤ Real.log T) :
    C * T ^ 2 * k ≤ C * T ^ 2 * Real.log T :=
  mul_le_mul_of_nonneg_left hk (by positivity)

end Qatlib.Papers.DiscreteSim08.MainResults
