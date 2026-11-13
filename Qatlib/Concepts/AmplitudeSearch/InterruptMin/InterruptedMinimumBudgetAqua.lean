/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.InterruptedMinimumBudgetStat
import Qatlib.Concepts.AmplitudeSearch.InterruptMin.InterruptedBudgetLaws
import Qatlib.Concepts.AmplitudeSearch.InterruptMin.InterruptedSearchAttemptAqua

/-!
# Budget guarantees for interrupted minimum search

This module proves the probability and budget laws of interrupted minimum search, including
preservation of a current global minimum and agreement between recursive evaluators and
probability laws. It compares interrupted success with atomic budget success.

The theorem `interrupted_charged_half` establishes success at least one half at `chargedBudget
N`, providing the charged-budget form of the minimum-finding guarantee in [DurrHoyer1996].

## Main statements

* `interrupted_minimum_expectation`: For nonnegative payoffs, expectation under the interrupted
  minimum-search law equals the embedded real evaluator.
* `interrupted_charged_half`: Uniformly initialized interrupted minimum search succeeds with
  probability at least one half at `chargedBudget N`, in the setting of [DurrHoyer1996].
* `interruptedMinimumBudget`: Establishes the probability, support, observation, comparison, and
  one-half success guarantees collected in `InterruptedMinimumBudget` [DurrHoyer1996].

## References

* [Dürr and Høyer, 1996][DurrHoyer1996]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.SearchStopping.UnknownCount

set_option autoImplicit false
namespace Qatlib.Concepts.AmplitudeSearch.InterruptMin
open Qatlib.Concepts.SearchStopping.GroverSuccess Qatlib.Concepts.SearchStopping.UnknownCount
open scoped ENNReal BigOperators Classical
variable {N : ℕ} {α : Type*} [LinearOrder α]

/-- The interrupted minimum-search evaluator is nonnegative for nonnegative payoffs. -/
theorem interrupted_minimum_nonneg (T : Fin N → α) (initialization : ℕ)
    (hN : 0 < N) (budget : ℕ) (current : Fin N) (payoff : Fin N → ℕ → ℝ)
    (hp : ∀ i r, 0 ≤ payoff i r) :
    0 ≤ interruptedMinimumEvalWithInit T initialization budget current payoff := by
  induction budget using Nat.strong_induction_on generalizing current with
  | h budget ih =>
    rw [interruptedMinimumEvalWithInit]
    split_ifs with hsingle hpaid
    · exact hp _ _
    · apply interrupted_eval_nonneg (by simpa using! hN) _ _
        (search_exponential_schedule N hN).2.1
      intro i r
      split_ifs with hr
      · exact ih r hr _
      · exact hp _ _
    · exact hp _ _

/-- The interrupted minimum-search evaluator sends the constant-one payoff to one. -/
theorem interrupted_minimum_one (T : Fin N → α) (initialization : ℕ)
    (hN : 0 < N) (budget : ℕ) (current : Fin N) :
    interruptedMinimumEvalWithInit T initialization budget current (fun _ _ => 1) = 1 := by
  induction budget using Nat.strong_induction_on generalizing current with
  | h budget ih =>
    rw [interruptedMinimumEvalWithInit]
    split_ifs with hsingle hpaid
    · rfl
    · have hf : (fun candidate remaining =>
          if _hr : remaining < budget then
            interruptedMinimumEvalWithInit T initialization remaining
              (checkedUpdate T current candidate) (fun _ _ => 1) else (1 : ℝ)) =
          (fun _ _ => 1) := by
        funext i r
        split_ifs with hr
        · exact ih r hr _
        · rfl
      rw [hf]
      exact interrupted_eval_one (by simpa using! hN) _ _
        (search_exponential_schedule N hN).2.1 _ _
    · rfl

/-- Every supported interrupted minimum-search result has remaining budget at most the initial
budget. -/
theorem interrupted_minimum_remaining (T : Fin N → α) (initialization : ℕ)
    (hN : 0 < N) (budget : ℕ) (current : Fin N) (x : Fin N × ℕ)
    (hx : x ∈ (interruptedMinimumPMFWithInit T initialization hN budget current).support) :
    x.2 ≤ budget := by
  induction budget using Nat.strong_induction_on generalizing current with
  | h budget ih =>
    rw [interruptedMinimumPMFWithInit] at hx
    split_ifs at hx with hsingle hpaid
    · have heq := (PMF.mem_support_pure_iff _ _).mp hx
      simp [heq]
    · obtain ⟨y, hy, hxy⟩ := (PMF.mem_support_bind_iff _ _ x).mp hx
      have hyr := interrupted_call_remaining (by simpa using! hN) (strictMarked T current)
        (ExponentialSizes N) (search_exponential_schedule N hN).2.1 0
        (budget - initialization) y hy
      have hyB : y.2 ≤ budget := hyr.trans (Nat.sub_le _ _)
      by_cases hr : y.2 < budget
      · rw [dif_pos hr] at hxy
        exact (ih y.2 hr _ hxy).trans hyB
      · rw [dif_neg hr] at hxy
        have heq := (PMF.mem_support_pure_iff _ _).mp hxy
        simpa [heq] using! hyB
    · have heq := (PMF.mem_support_pure_iff _ _).mp hx
      simp [heq]

/-- If the current index is a global minimum, every supported interrupted minimum-search result
retains that index. -/
theorem interrupted_minimum_output (T : Fin N → α) (initialization : ℕ)
    (hN : 0 < N) (budget : ℕ) (current : Fin N) (hmin : ∀ j, T current ≤ T j)
    (x : Fin N × ℕ)
    (hx : x ∈ (interruptedMinimumPMFWithInit T initialization hN budget current).support) :
    x.1 = current := by
  induction budget using Nat.strong_induction_on generalizing current with
  | h budget ih =>
    rw [interruptedMinimumPMFWithInit] at hx
    split_ifs at hx with hsingle hpaid
    · exact congrArg Prod.fst ((PMF.mem_support_pure_iff _ _).mp hx)
    · obtain ⟨y, _, hxy⟩ := (PMF.mem_support_bind_iff _ _ x).mp hx
      have hu := checkedUpdate_preserves_minimum T current y.1 hmin
      simp only [hu] at hxy
      by_cases hr : y.2 < budget
      · rw [dif_pos hr] at hxy
        exact ih y.2 hr current hmin hxy
      · rw [dif_neg hr] at hxy
        exact congrArg Prod.fst ((PMF.mem_support_pure_iff _ _).mp hxy)
    · exact congrArg Prod.fst ((PMF.mem_support_pure_iff _ _).mp hx)

/-- For nonnegative payoffs, expectation under the interrupted minimum-search law equals the
embedded real evaluator. -/
theorem interrupted_minimum_expectation (T : Fin N → α) (initialization : ℕ)
    (hN : 0 < N) (budget : ℕ) (current : Fin N) (payoff : Fin N → ℕ → ℝ)
    (hp : ∀ i r, 0 ≤ payoff i r) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (interruptedMinimumPMFWithInit T initialization hN budget current)
      (fun x => ENNReal.ofReal (payoff x.1 x.2)) =
      ENNReal.ofReal (interruptedMinimumEvalWithInit T initialization budget current payoff) := by
  induction budget using Nat.strong_induction_on generalizing current with
  | h budget ih =>
    rw [interruptedMinimumPMFWithInit, interruptedMinimumEvalWithInit]
    split_ifs with hsingle hpaid
    · exact Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure _ _
    · rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
      let s : Fin N → ℕ → ℝ := fun i r => if _hr : r < budget then
        interruptedMinimumEvalWithInit T initialization r (checkedUpdate T current i) payoff
        else payoff (checkedUpdate T current i) r
      have he (x : Fin N × ℕ) :
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
            (if _hr : x.2 < budget then
              interruptedMinimumPMFWithInit T initialization hN x.2 (checkedUpdate T current x.1)
            else PMF.pure (checkedUpdate T current x.1, x.2))
            (fun x => ENNReal.ofReal (payoff x.1 x.2)) = ENNReal.ofReal (s x.1 x.2) := by
        by_cases hr : x.2 < budget
        · simp only [dif_pos hr, s]
          exact ih x.2 hr _
        · simp only [dif_neg hr, s]
          exact Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure _ _
      simp_rw [he]
      exact interrupted_call_expectation (by simpa using! hN) _ _
        (search_exponential_schedule N hN).2.1 _ _ s (by
          intro i r
          dsimp only [s]
          split_ifs
          · exact interrupted_minimum_nonneg T initialization hN r _ payoff hp
          · exact hp _ _)
    · exact Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure _ _

/-- The interrupted minimum-search evaluator preserves pointwise order of payoffs. -/
theorem interrupted_minimum_mono (T : Fin N → α) (initialization : ℕ)
    (hN : 0 < N) (budget : ℕ) (current : Fin N) (f g : Fin N → ℕ → ℝ)
    (hfg : ∀ i r, f i r ≤ g i r) :
    interruptedMinimumEvalWithInit T initialization budget current f ≤
      interruptedMinimumEvalWithInit T initialization budget current g := by
  induction budget using Nat.strong_induction_on generalizing current with
  | h budget ih =>
    conv_lhs => rw [interruptedMinimumEvalWithInit]
    conv_rhs => rw [interruptedMinimumEvalWithInit]
    split_ifs with hsingle hpaid
    · exact hfg _ _
    · apply interrupted_eval_mono (by simpa using! hN) _ _
        (search_exponential_schedule N hN).2.1
      intro i r
      split_ifs with hr
      · exact ih r hr _
      · exact hfg _ _
    · exact hfg _ _

/-- Interrupted minimum search succeeds with probability one when its current index is already a
global minimum. -/
theorem interrupted_success_of_minimum (T : Fin N → α) (initialization : ℕ)
    (hN : 0 < N) (budget : ℕ) (current : Fin N) (hmin : ∀ j, T current ≤ T j) :
    interruptedMinimumSuccessWithInit T initialization budget current = 1 := by
  unfold interruptedMinimumSuccessWithInit
  induction budget using Nat.strong_induction_on generalizing current with
  | h budget ih =>
    rw [interruptedMinimumEvalWithInit]
    split_ifs with hsingle hpaid
    · rfl
    · have hf : (fun candidate remaining =>
          if _hr : remaining < budget then
            interruptedMinimumEvalWithInit T initialization remaining
              (checkedUpdate T current candidate) (fun i _ => if ∀ j, T i ≤ T j then 1 else 0)
          else (if ∀ j, T (checkedUpdate T current candidate) ≤ T j then (1 : ℝ) else 0)) =
          (fun _ _ => 1) := by
        funext i r
        simp only [checkedUpdate_preserves_minimum T current i hmin]
        split_ifs with hr
        · exact ih r hr current hmin
        · rfl
      rw [hf]
      exact interrupted_eval_one (by simpa using! hN) _ _
        (search_exponential_schedule N hN).2.1 _ _
    · rfl

/-- The current index's minimum indicator is bounded by the interrupted minimum-search success
probability. -/
theorem interrupted_success_indicator_le (T : Fin N → α) (initialization : ℕ)
    (hN : 0 < N) (budget : ℕ) (current : Fin N) :
    (if ∀ j, T current ≤ T j then (1 : ℝ) else 0) ≤
      interruptedMinimumSuccessWithInit T initialization budget current := by
  by_cases hm : ∀ j, T current ≤ T j
  · rw [if_pos hm, interrupted_success_of_minimum T initialization hN budget current hm]
  · rw [if_neg hm]
    exact interrupted_minimum_nonneg T initialization hN budget current _ (by intro i r; positivity)

/-- Interrupted minimum-search success is at least the atomic finite-budget success with the
same initialization charge. -/
theorem interrupted_success_dominates (T : Fin N → α) (initialization : ℕ)
    (hN : 0 < N) (budget : ℕ) (current : Fin N) :
    minimumBudgetSuccessWithInit T initialization budget current ≤
      interruptedMinimumSuccessWithInit T initialization budget current := by
  induction budget using Nat.strong_induction_on generalizing current with
  | h budget ih =>
    unfold minimumBudgetSuccessWithInit interruptedMinimumSuccessWithInit
    rw [minimumBudgetEvalWithInit, interruptedMinimumEvalWithInit]
    by_cases hsingle : N = 1
    · rw [if_pos hsingle, if_pos hsingle]
    · rw [if_neg hsingle, if_neg hsingle]
      by_cases hpaid : initialization ≤ budget
      · rw [if_pos hpaid, if_pos hpaid]
        apply interrupted_dominates_atomic (by simpa using! hN) _ _
          (search_exponential_schedule N hN).2.1
        · intro i r hr
          have hrB : r < budget := hr.trans_le (Nat.sub_le _ _)
          simp only [dif_pos hrB]
          exact ih r hrB _
        · intro i r _
          by_cases hm : ∀ j, T current ≤ T j
          · have hu := checkedUpdate_preserves_minimum T current i hm
            simp only [if_pos hm, hu]
            split_ifs with hr
            · exact le_of_eq (interrupted_success_of_minimum T initialization hN 0 current hm).symm
            · exact le_rfl
          · simp only [if_neg hm]
            by_cases hr : 0 < budget
            · rw [dif_pos hr]
              exact interrupted_minimum_nonneg T initialization hN 0 _ _ (by intro i r; positivity)
            · rw [dif_neg hr]
              split_ifs <;> norm_num
      · rw [if_neg hpaid, if_neg hpaid]

/-- The partial observation mass on strictly improving indices equals the observed acceptance
probability of the interrupted phase attempt. -/
theorem interrupted_observation_acceptance (T : Fin N → α) (hN : 0 < N)
    (current : Fin N) (j r : ℕ) :
    (∑ i ∈ strictMarked T current, partialObsMass (strictMarked T current) j r i) =
      observedAcceptance
        (BitOracleOn fun x : Fin N => decide (x ∈ strictMarked T current))
        (interruptedSearchPhaseAttempt (strictMarked T current) j r)
        (WithMinus (Uniform (Fin N))) := by
  rw [(interruptedSearchAttempt (Fin N) (by simpa using! hN) (strictMarked T current) j r).1]
  unfold partialObsMass partialState MeasureProb
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_product]
  simp

/-- Uniformly initialized interrupted minimum search succeeds with probability at least one half
at `chargedBudget N`, in the setting of [DurrHoyer1996]. -/
theorem interrupted_charged_half (T : Fin N → α) (hN : 0 < N) :
    (1 / 2 : ℝ) ≤ interruptedChargedInitialSuccess T (chargedBudget N) := by
  apply (charged_initial_success_half T hN).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact Finset.sum_le_sum fun i _ => interrupted_success_dominates T (initCharge N) hN _ i

/-- The uniformly initialized interrupted minimum-search success probability is at most one. -/
theorem interrupted_charged_le_one (T : Fin N → α) (hN : 0 < N) (budget : ℕ) :
    interruptedChargedInitialSuccess T budget ≤ 1 := by
  have hs : (∑ i : Fin N, interruptedMinimumSuccessWithInit T (initCharge N) budget i) ≤
      ∑ _i : Fin N, (1 : ℝ) := by
    apply Finset.sum_le_sum
    intro i _
    apply le_trans (interrupted_minimum_mono T (initCharge N) hN budget i
      (fun i _ => if ∀ j, T i ≤ T j then 1 else 0) (fun _ _ => 1) (by intro i r; (try dsimp only); split_ifs <;> norm_num))
    exact le_of_eq (interrupted_minimum_one T (initCharge N) hN budget i)
  have h := div_le_div_of_nonneg_right hs (Nat.cast_nonneg N)
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simpa only [interruptedChargedInitialSuccess, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, div_self hn] using! h

/-- Establishes the probability, support, observation, comparison, and one-half success
guarantees collected in `InterruptedMinimumBudget` [DurrHoyer1996]. -/
theorem interruptedMinimumBudget : InterruptedMinimumBudget := by
  intro N hN α _ T
  exact ⟨fun initialization budget current payoff hp =>
      interrupted_minimum_nonneg T initialization hN budget current payoff hp,
    fun initialization budget current => interrupted_minimum_one T initialization hN budget current,
    fun budget current x hx => interrupted_minimum_remaining T (initCharge N) hN budget current x hx,
    fun budget current hm x hx => interrupted_minimum_output T (initCharge N) hN budget current hm x hx,
    fun budget current payoff hp => interrupted_minimum_expectation T (initCharge N) hN budget current payoff hp,
    fun current j r => interrupted_observation_acceptance T hN current j r,
    fun budget current => interrupted_success_dominates T (initCharge N) hN budget current,
    interrupted_charged_half T hN, interrupted_charged_le_one T hN _⟩

end Qatlib.Concepts.AmplitudeSearch.InterruptMin
