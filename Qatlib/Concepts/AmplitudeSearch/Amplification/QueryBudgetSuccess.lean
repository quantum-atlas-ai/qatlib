/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.BudgetCoupling
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Minimum search with a square-root query budget

This module defines `minimumQueryBudget` as the ceiling of `58 * Real.sqrt N` and averages
budgeted success over the initial index in `minimumInitialSuccess`. The first-moment completion
bound yields success probability at least one half for every nonempty finite table, in the
minimum-finding setting of [DurrHoyer1996].

## Main statements

* `minimum_initial_success_half`: proves the one-half success bound at the chosen query budget.
* `minimumQueryBudget_le`: bounds the integer query budget by `59 * Real.sqrt N`.
* `minimumQueryBudget_isBigO_sqrt`: expresses the asymptotic square-root query bound.

## References

* [Dürr and Høyer, 1996][DurrHoyer1996]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeSearch.InterruptMin.PlannedRetry

open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment
open Qatlib.Concepts.AmplitudeSearch.Amplification.RankedCallLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification.SortedRankedTable

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

/-- The integer query budget obtained by rounding `58 * Real.sqrt N` upward. -/
noncomputable def minimumQueryBudget (N : ℕ) : ℕ := Nat.ceil ((58 : ℝ) * Real.sqrt N)

/-- The average of `minimumBudgetSuccess` over a uniformly chosen initial table index. -/
noncomputable def minimumInitialSuccess {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (budget : ℕ) : ℝ :=
  (∑ current : Fin N, minimumBudgetSuccess T budget current) / (N : ℝ)

/-- For a nonempty table, the average budgeted success probability lies between zero and one. -/
theorem minimumInitialSuccess_bounds {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (budget : ℕ) :
    0 ≤ minimumInitialSuccess T budget ∧ minimumInitialSuccess T budget ≤ 1 := by
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun i _ => (minimumBudgetSuccess_bounds T hN budget i).1))
      (Nat.cast_nonneg N)
  · have hs : (∑ i : Fin N, minimumBudgetSuccess T budget i) ≤ ∑ _i : Fin N, (1 : ℝ) :=
      Finset.sum_le_sum (fun i _ => (minimumBudgetSuccess_bounds T hN budget i).2)
    have h := div_le_div_of_nonneg_right hs (Nat.cast_nonneg N)
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    simpa only [minimumInitialSuccess, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, div_self hn] using! h

/-- For `N > 0`, the initial masses of runs fitting the query budget sum to the average
completion mass over initial ranks. -/
theorem initial_queryCompletion_hasSum {N : ℕ} (e : Fin N ≃ Fin N) (skip : RankSkip N)
    (hN : 0 < N) (budget : ℕ) :
    HasSum (fun x : Fin N × List (SearchTrace N) => if runQueries x.2 ≤ budget then
      (queryBBHTLaw e).initialMass skip x else 0)
      ((∑ i : Fin N, queryCompletion e skip (skip.next i) budget) / (N : ℝ)) := by
  have hfib (i : Fin N) : HasSum (fun xs : List (SearchTrace N) => if runQueries xs ≤ budget then
      (queryBBHTLaw e).initialMass skip (i, xs) else 0)
      (queryCompletion e skip (skip.next i) budget / (N : ℝ)) := by
    have h := (queryCompletion_law e skip (skip.next i)
      (lt_of_le_of_lt (skip.le_rank i) i.isLt) budget).1.div_const (N : ℝ)
    convert! h using 1
    funext xs
    unfold RankedCallLaw.initialMass
    split_ifs <;> ring
  have hrows : HasSum (fun i : Fin N => queryCompletion e skip (skip.next i) budget / (N : ℝ))
      ((∑ i : Fin N, queryCompletion e skip (skip.next i) budget) / (N : ℝ)) := by
    rw [Finset.sum_div]
    exact hasSum_fintype _
  apply nonnegative_product_sum _ _ _ _ hfib hrows
  intro i xs

  split_ifs
  · exact ((queryBBHTLaw e).initialMass_normalized skip hN).2 (i, xs)
  · exact le_rfl

/-- For every nonempty finite table, budgeted minimum search succeeds with probability at least
one half at `minimumQueryBudget N`. This supplies a square-root query guarantee in the
setting of [DurrHoyer1996]. -/
theorem minimum_initial_success_half {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) :
    (1 / 2 : ℝ) ≤ minimumInitialSuccess T (minimumQueryBudget N) := by
  let ranked := SortedRankedTable.ofTable T
  let law := queryBBHTLaw ranked.indexOfRank
  let B := minimumQueryBudget N
  have hceil : (58 : ℝ) * Real.sqrt N ≤ (B : ℝ) := Nat.le_ceil _
  obtain ⟨q, hq, _, hqb⟩ := bbht_query_attainment_moment ranked hN
  have hm : (0 : ℝ) < (B : ℝ) / 2 := by
    have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hN)
    nlinarith
  have hqm : q ≤ (B : ℝ) / 2 := by linarith
  obtain ⟨p, hp, hhalf, _⟩ := nonnegative_clock_half_mass
    (law.initialMass ranked.skip) (fun x : Fin N × List (SearchTrace N) => law.runClock x.2)
    (law.initialMass_normalized ranked.skip hN).1
    (law.initialMass_normalized ranked.skip hN).2
    (fun x => law.runClock_nonneg x.2) q ((B : ℝ) / 2) hq hqm hm
  have htwo : 2 * ((B : ℝ) / 2) = (B : ℝ) := by ring
  change HasSum (fun x : Fin N × List (SearchTrace N) =>
    if (queryBBHTLaw ranked.indexOfRank).runClock x.2 ≤ 2 * ((B : ℝ) / 2) then
      (queryBBHTLaw ranked.indexOfRank).initialMass ranked.skip x else 0) p at hp
  simp only [queryBBHTLaw_clock, htwo, Nat.cast_le] at hp
  have heq := hp.unique (initial_queryCompletion_hasSum ranked.indexOfRank ranked.skip hN B)
  rw [heq] at hhalf
  have hsums := Finset.sum_le_sum (fun i (_hi : i ∈ Finset.univ) =>
    queryCompletion_le_actual_success ranked hN i B)
  have hd := div_le_div_of_nonneg_right hsums (Nat.cast_nonneg N)
  rw [ranked.indexOfRank.sum_comp] at hd
  exact hhalf.trans hd

/-- For `N > 0`, the rounded query budget is at most `59 * Real.sqrt N`. -/
theorem minimumQueryBudget_le (N : ℕ) (hN : 0 < N) :
    (minimumQueryBudget N : ℝ) ≤ 59 * Real.sqrt N := by
  have hc := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 58 * Real.sqrt N)
  have hs : (1 : ℝ) ≤ Real.sqrt N := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ N by exact_mod_cast hN)
    simpa using! h
  unfold minimumQueryBudget
  linarith

/-- The minimum-search query budget grows as `O(√N)` as `N` tends to infinity. -/
theorem minimumQueryBudget_isBigO_sqrt :
    Asymptotics.IsBigO Filter.atTop (fun N : ℕ => (minimumQueryBudget N : ℝ))
      (fun N : ℕ => Real.sqrt (N : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound (59 : ℝ) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  simpa only [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ (minimumQueryBudget N : ℝ) from Nat.cast_nonneg _),
    abs_of_nonneg (Real.sqrt_nonneg (N : ℝ))] using! minimumQueryBudget_le N hN

end Qatlib.Concepts.AmplitudeSearch.Amplification
