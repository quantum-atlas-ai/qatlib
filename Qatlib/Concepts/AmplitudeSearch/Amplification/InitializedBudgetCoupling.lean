/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.MinimumBudgetCore
import Qatlib.Concepts.AmplitudeSearch.Amplification.CompletionLaw
import Qatlib.Concepts.AmplitudeSearch.Amplification.QueryClock

/-!
# Initialized budget coupling for BBHT runs

`initializedBBHTLaw` charges a fixed initialization amount in addition to each terminal
Boolean-query cost. The module unfolds the corresponding budgeted minimum-finding procedure
after paying initialization and compares ranked-run completion with actual success.

The construction connects explicit initialization costs to the BBHT search and quantum
minimum-finding framework of [BoyerEtAl1998] and [DurrHoyer1996].

## Main statements

* `minimumBudgetSuccessWithInit_step`: unfolds an affordable initialized search call.
* `initializedCompletion_le_actual_success`: couples initialized completion mass to actual
  success.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
* [Durr and Hoyer, 1996][DurrHoyer1996]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeSearch.Amplification.RankedCallLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification.SortedRankedTable

open Qatlib.Concepts.AmplitudeSearch.InterruptMin

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib
open Qatlib.Concepts.SearchStopping.GroverSuccess
open Qatlib.Concepts.SearchStopping.UnknownCount
open Qatlib
/-- The ranked BBHT law charging a fixed initialization cost plus the terminal Boolean query
count for each call. -/
noncomputable def initializedBBHTLaw {N : ℕ} (e : Fin N ≃ Fin N) (initialization : ℕ) :
    RankedCallLaw N (SearchTrace N) :=
  bbhtJointLaw e (fun x => ((initialization + TerminalBooleanQueries (ExponentialSizes N) x : ℕ) : ℝ))
    (fun _ => Nat.cast_nonneg _)

variable {N : ℕ} {α : Type*} [LinearOrder α]

/-- When initialization fits the budget and `N ≠ 1`, initialized minimum-finding success unfolds
into a finite-budget search on the remaining budget followed by checked recursion. -/
theorem minimumBudgetSuccessWithInit_step (T : Fin N → α) (hN1 : N ≠ 1)
    (initialization budget : ℕ) (hpaid : initialization ≤ budget) (current : Fin N) :
    minimumBudgetSuccessWithInit T initialization budget current =
      FiniteBudgetEval (strictMarked T current) (ExponentialSizes N) 0 (budget - initialization)
        (fun candidate remaining => if remaining < budget then
          minimumBudgetSuccessWithInit T initialization remaining (checkedUpdate T current candidate) else 0)
        (fun _ => if ∀ j, T current ≤ T j then 1 else 0) := by
  rw [minimumBudgetSuccessWithInit, minimumBudgetEvalWithInit, if_neg hN1, if_pos hpaid]
  rfl

/-- For a sorted ranked table, completion mass under initialization-plus-query charges is
bounded by the actual initialized minimum-finding success probability. -/
theorem initializedCompletion_le_actual_success (T : SortedRankedTable N α) (hN : 0 < N)
    (initialization : ℕ) (initial : Fin N) (budget : ℕ) :
    (initializedBBHTLaw T.indexOfRank initialization).completionMass T.skip
      (fun x => initialization + TerminalBooleanQueries (ExponentialSizes N) x)
      (T.skip.next initial) budget ≤
        minimumBudgetSuccessWithInit T.value initialization budget (T.indexOfRank initial) := by
  let law := initializedBBHTLaw T.indexOfRank initialization
  let charge : SearchTrace N → ℕ :=
      fun x => initialization + TerminalBooleanQueries (ExponentialSizes N) x
  have hall : ∀ t : ℕ, ∀ y : Fin N, T.skip.next y = t → ∀ b,
      law.completionMass T.skip charge t b ≤
        minimumBudgetSuccessWithInit T.value initialization b (T.indexOfRank y) := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro y hy b
      cases t with
      | zero =>
        rw [law.completion_zero T.skip charge hN]
        rw [minimumBudgetSuccessWithInit_of_minimum T.value initialization hN b (T.indexOfRank y)
          ((T.lowerCut_zero_iff_minimum y).mp hy)]
      | succ t =>
        have htN : t + 1 < N := by
          rw [← hy]
          exact lt_of_le_of_lt (T.skip.le_rank y) y.isLt
        have hc := law.completion_step T.skip charge (t + 1) (by omega) htN b
        by_cases hpaid : initialization ≤ b
        · let A := strictMarked T.value (T.indexOfRank y)
          let S : Fin N → ℕ → ℝ := fun candidate remaining => if remaining < b then
            minimumBudgetSuccessWithInit T.value initialization remaining
              (checkedUpdate T.value (T.indexOfRank y) candidate) else 0
          let timeout : ℕ → ℝ :=
              fun _ => if ∀ j, T.value (T.indexOfRank y) ≤ T.value j then 1 else 0
          have hN1 : N ≠ 1 := by omega
          have hmarked : A = rankMarked T.indexOfRank (t + 1) := by
            have h := rankMarked_eq_strict_values T y
            change rankMarked T.indexOfRank (T.skip.next y) = A at h
            rw [hy] at h
            exact h.symm
          have hm (x : SearchTrace N) : law.mass (t + 1) x =
              TerminalMass A (ExponentialSizes N) x := by
            simp only [law, initializedBBHTLaw, bbhtJointLaw,
              if_pos (show 0 < t + 1 ∧ t + 1 < N from ⟨by omega, htN⟩), ← hmarked]
          have hS (i : Fin N) (r : ℕ) : 0 ≤ S i r ∧ S i r ≤ 1 := by
            dsimp [S]
            split_ifs
            · exact minimumBudgetSuccessWithInit_bounds T.value initialization hN r _
            · norm_num
          have htimeout (r : ℕ) : 0 ≤ timeout r := by dsimp [timeout]; split_ifs <;> norm_num
          let f : SearchTrace N → ℝ := fun x =>
            if TerminalBooleanQueries (ExponentialSizes N) x ≤ b - initialization then
              TerminalMass A (ExponentialSizes N) x * S (TerminalOutput x)
                ((b - initialization) - TerminalBooleanQueries (ExponentialSizes N) x) else 0
          have hf (x : SearchTrace N) : 0 ≤ f x ∧ f x ≤ law.mass (t + 1) x := by
            have hmass := law.mass_nonneg (t + 1) htN x
            dsimp [f]
            rw [← hm]
            split_ifs
            · constructor
              · exact mul_nonneg hmass (hS _ _).1
              · simpa only [mul_one] using mul_le_mul_of_nonneg_left (hS _ _).2 hmass
            · exact ⟨le_rfl, hmass⟩
          have hfs := Summable.of_nonneg_of_le (fun x => (hf x).1) (fun x => (hf x).2)
            (law.normalized (t + 1) (by omega) htN).summable
          have hpoint (x : SearchTrace N) :
              (if charge x ≤ b then law.mass (t + 1) x * law.completionMass T.skip charge
                (T.skip.next (law.outputRank x)) (b - charge x) else 0) ≤ f x := by
            dsimp [f]
            by_cases hcost : TerminalBooleanQueries (ExponentialSizes N) x ≤ b - initialization
            · have htotal : charge x ≤ b := by dsimp [charge]; omega
              simp only [if_pos hcost, if_pos htotal]
              rw [← hm]
              have hr : (b - initialization) - TerminalBooleanQueries (ExponentialSizes N) x < b := by
                have hp := terminalQueries_pos x
                omega
              have hrem : b - charge x =
                  (b - initialization) - TerminalBooleanQueries (ExponentialSizes N) x := by
                dsimp [charge]
                omega
              simp only [S, if_pos hr]
              rw [hrem]
              by_cases hx : (law.outputRank x).val < t + 1
              · have hnext : T.skip.next (law.outputRank x) < t + 1 :=
                  lt_of_le_of_lt (T.skip.le_rank _) hx
                have hlow : T.value (T.indexOfRank (law.outputRank x)) < T.value (T.indexOfRank y) := by
                  apply (T.smaller_iff_lowerCut y _).mpr
                  change (law.outputRank x).val < T.skip.next y
                  rwa [hy]
                have hout : T.indexOfRank (law.outputRank x) = TerminalOutput x :=
                  T.indexOfRank.apply_symm_apply _
                have hcheck : checkedUpdate T.value (T.indexOfRank y) (TerminalOutput x) = TerminalOutput x := by
                  apply if_pos
                  rwa [hout] at hlow
                rw [hcheck]
                apply mul_le_mul_of_nonneg_left _ (law.mass_nonneg (t + 1) htN x)
                have h := ih _ hnext (law.outputRank x) rfl
                  ((b - initialization) - TerminalBooleanQueries (ExponentialSizes N) x)
                rwa [hout] at h
              · rw [law.lower_support (t + 1) (by omega) htN x hx]
                simp
            · have htotal : ¬ charge x ≤ b := by dsimp [charge]; omega
              simp only [if_neg hcost, if_neg htotal, le_refl]
          have hsums := Summable.tsum_le_tsum hpoint hc.summable hfs
          rw [hc.tsum_eq] at hsums
          have hdom := search_finite_budget_eval_dominates_terminal (by simpa using hN)
            A (ExponentialSizes N) (search_exponential_schedule N hN).2.1 (b - initialization)
            S timeout (fun i r => (hS i r).1) htimeout
          calc
            _ ≤ ∑' x, f x := hsums
            _ ≤ FiniteBudgetEval A (ExponentialSizes N) 0 (b - initialization) S timeout := hdom
            _ = minimumBudgetSuccessWithInit T.value initialization b (T.indexOfRank y) :=
              (minimumBudgetSuccessWithInit_step T.value hN1 initialization b hpaid (T.indexOfRank y)).symm
        · have heq : (fun x : SearchTrace N => if charge x ≤ b then law.mass (t + 1) x *
              law.completionMass T.skip charge (T.skip.next (law.outputRank x)) (b - charge x) else 0) =
              fun _ => 0 := by
            funext x
            have hx : ¬ charge x ≤ b := by dsimp [charge]; omega
            simp only [if_neg hx]
          rw [heq] at hc
          have hz := hc.unique (hasSum_zero : HasSum (fun _ : SearchTrace N => (0 : ℝ)) 0)
          rw [hz]
          exact (minimumBudgetSuccessWithInit_bounds T.value initialization hN b (T.indexOfRank y)).1
  exact hall _ initial rfl budget

end Qatlib.Concepts.AmplitudeSearch.Amplification
