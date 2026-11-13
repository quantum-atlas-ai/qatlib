/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Real.Sqrt
import Qatlib.Concepts.SearchStopping.RestartLaw.Section3RestartExpectedSubgoalTigh
import Qatlib.Concepts.SearchStopping.UnknownCount.Theorem3CorrectedTigh
import Qatlib.Concepts.QueryComplexity.AdaptiveInfo.NeedleSearch

/-!
# Expected costs for search with an unknown marked count

This module connects the unknown-count search discussion of [HoyerMoscaDeWolf2003] with the
imported terminal-trace analysis for an exact oracle. `unknown_count_expected_iterations` gives
a `HasSum` witness for the exponential schedule's expected iteration cost, bounded by `(9 / 2) *
Real.sqrt (N / t)` for a nonempty marked set. `unknown_count_expected_cost_le` combines this
witness with a conditional geometric restart estimate.

`restarts_failure_tendsto_zero` controls the scalar failure powers for a fixed positive success
parameter. `classical_half_success_requires_linear_queries` gives a query lower bound for finite
mixtures of classical needle-search trees, and `quantum_cost_below_classical` compares the
square-root cost expression with `N / 2` when `N ≥ 81`.

## Main statements

* `unknown_count_expected_cost_le`: the terminal-trace sum and conditional restart cost bound.
* `classical_half_success_requires_linear_queries`: the lower bound for classical needle search.
* `quantum_cost_below_classical`: the scalar square-root comparison for `N ≥ 81`.

## References

* [Høyer et al., 2003][HoyerMoscaDeWolf2003]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.BndErrSearch03.MainResults.UnknownCountSearch

open Qatlib.Concepts.SearchStopping.RestartLaw

/-- For nonnegative per-run cost `c` and `1/576 ≤ p ≤ 1`, the displayed geometric restart cost
series is at most `576 * c`. -/
theorem restarts_cost_le (c p : ℝ) (hc : 0 ≤ c)
    (hp : (1 / 576 : ℝ) ≤ p) (hp1 : p ≤ 1) :
    (∑' r : ℕ, ((r + 1 : ℕ) : ℝ) * c * ((1 - p) ^ r * p)) ≤ 576 * c := by
  have hp0 : 0 < p := by linarith
  rw [geometric_restart_expectation p c hp0 hp1]
  rw [div_le_iff₀ hp0]
  nlinarith [hc, hp]

open Qatlib.Concepts.AmplitudeSearch.InterruptMin
open Qatlib.Concepts.SearchStopping.UnknownCount

/-- For a nonempty marked set in a finite nonempty index type, the exponential schedule's
terminal-mass-weighted iteration costs have a nonnegative sum `q ≤ (9 / 2) * Real.sqrt (N /
t)`, where `N` is the index cardinality and `t` the marked cardinality. -/
theorem unknown_count_expected_iterations {I : Type} [Fintype I] [DecidableEq I]
    (hI : 0 < Fintype.card I) (A : Finset I) (hA : 0 < A.card) :
    ∃ q : ℝ, HasSum
      (fun x : TerminalTrace I (ExponentialSizes (Fintype.card I)) =>
        TerminalMass A (ExponentialSizes (Fintype.card I)) x *
          (TerminalCost (ExponentialSizes (Fintype.card I)) x : ℝ)) q ∧
      0 ≤ q ∧ q ≤ (9 / 2 : ℝ) * Real.sqrt ((Fintype.card I : ℝ) / A.card) := by
  have h := Qatlib.Concepts.SearchStopping.UnknownCount.theorem3Corrected
    (I := I) hI
  dsimp only at h
  exact (h.1 A hA).2.2.2.1

/-- Provides a nonnegative terminal-trace expected iteration cost at most `(9 / 2) * Real.sqrt
(N / t)` and bounds its geometric restart series by 576 times that expression whenever
`1/576 ≤ p ≤ 1`. This combines exact-oracle unknown-count iteration costs with a conditional
restart estimate for the discussion in [HoyerMoscaDeWolf2003]. -/
theorem unknown_count_expected_cost_le {I : Type} [Fintype I] [DecidableEq I]
    (hI : 0 < Fintype.card I) (A : Finset I) (hA : 0 < A.card) :
    ∃ q : ℝ, HasSum
      (fun x : TerminalTrace I (ExponentialSizes (Fintype.card I)) =>
        TerminalMass A (ExponentialSizes (Fintype.card I)) x *
          (TerminalCost (ExponentialSizes (Fintype.card I)) x : ℝ)) q ∧
      0 ≤ q ∧ q ≤ (9 / 2 : ℝ) * Real.sqrt ((Fintype.card I : ℝ) / A.card) ∧
      ∀ p : ℝ, (1 / 576 : ℝ) ≤ p → p ≤ 1 →
        (∑' r : ℕ, ((r + 1 : ℕ) : ℝ) * q * ((1 - p) ^ r * p))
          ≤ 576 * ((9 / 2 : ℝ) * Real.sqrt ((Fintype.card I : ℝ) / A.card)) := by
  obtain ⟨q, hsum, hq0, hqle⟩ := unknown_count_expected_iterations hI A hA
  refine ⟨q, hsum, hq0, hqle, ?_⟩
  intro p hp hp1
  have h1 : (∑' r : ℕ, ((r + 1 : ℕ) : ℝ) * q * ((1 - p) ^ r * p)) ≤ 576 * q :=
    restarts_cost_le q p hq0 hp hp1
  have h2 : 576 * q ≤ 576 * ((9 / 2 : ℝ) * Real.sqrt ((Fintype.card I : ℝ) / A.card)) :=
    mul_le_mul_of_nonneg_left hqle (by norm_num)
  linarith

/-- For `0 < p ≤ 1`, the scalar failure powers `(1 - p) ^ r` tend to zero. This supplies the
fixed-success-parameter repetition limit relevant to [HoyerMoscaDeWolf2003]. -/
theorem restarts_failure_tendsto_zero (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    Filter.Tendsto (fun r : ℕ => (1 - p) ^ r) Filter.atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)

/-- For `0 < t ≤ N`, the square root of `N / t` is at most `N / t`. -/
theorem sqrt_ratio_le_ratio (N t : ℝ) (ht : 0 < t) (htN : t ≤ N) :
    Real.sqrt (N / t) ≤ N / t := by
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le ht htN
  have hx0 : (0 : ℝ) ≤ N / t := le_of_lt (div_pos hNpos ht)
  rw [Real.sqrt_le_left hx0]
  have hx1 : 1 ≤ N / t := (one_le_div ht).mpr htN
  simpa [one_mul, pow_two] using mul_le_mul_of_nonneg_left hx1 hx0

open Qatlib.Concepts.QueryComplexity.AdaptiveInfo.ClassicalDefs

/-- A finite probability mixture of classical needle-search trees, each using at most `M`
queries on every target, can have uniform success at least one half only if `N / 2 ≤ M + 1`.
This provides a classical query benchmark for the search discussion in
[HoyerMoscaDeWolf2003]. -/
theorem classical_half_success_requires_linear_queries {I S : Type} [Fintype I]
    [DecidableEq I] [Fintype S] (weight : S → ℝ) (tree : S → QueryTree I Bool I)
    (M : ℕ) (hI : 0 < Fintype.card I) (hw : ∀ s, 0 ≤ weight s)
    (hmass : ∑ s, weight s = 1)
    (hcost : ∀ s y, (run (needleOracle y) (tree s)).2 ≤ M)
    (hsucc : (1 / 2 : ℝ) ≤ ∑ s, weight s * needleSuccess (tree s)) :
    (Fintype.card I : ℝ) / 2 ≤ (M : ℝ) + 1 := by
  have h := randomized_needle_success_upper weight tree M hw hmass hcost
  have hN : (0 : ℝ) < (Fintype.card I : ℝ) := by exact_mod_cast hI
  have hge : (1 / 2 : ℝ) ≤ ((M : ℝ) + 1) / Fintype.card I := le_trans hsucc h
  rw [le_div_iff₀ hN] at hge
  linarith

/-- For natural `N ≥ 81`, the scalar expression `(9 / 2) * Real.sqrt N` is at most `N / 2`. This
is the numerical comparison used alongside the classical bound in [HoyerMoscaDeWolf2003]. -/
theorem quantum_cost_below_classical (N : ℕ) (hN : 81 ≤ N) :
    (9 / 2 : ℝ) * Real.sqrt N ≤ (N : ℝ) / 2 := by
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hN81 : (81 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hsqrt : Real.sqrt (N : ℝ) ≤ (N : ℝ) / 9 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [mul_nonneg hN0 (sub_nonneg.mpr hN81)]
  nlinarith

end Qatlib.Papers.BndErrSearch03.MainResults.UnknownCountSearch
