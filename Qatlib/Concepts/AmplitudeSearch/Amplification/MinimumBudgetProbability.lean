/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.ChargedBudgetSuccess
import Qatlib.Concepts.AmplitudeSearch.InterruptMin.SearchBudgetProbability

/-!
# Probability laws for budgeted minimum search

This module constructs `minimumBudgetPMFWithInit`, the joint law of the returned index and
remaining budget for recursive quantum minimum search [DurrHoyer1996]. It identifies
expectations and event probabilities with the corresponding finite-budget evaluator.

The costed law records the spent budget, while `chargedInitialPMF` adds uniform initial-index
sampling and the prescribed initialization charge. The resulting success event has probability
at least one half at `chargedBudget`.

## Main statements

* `minimumBudgetPMFWithInit_expectation`: connects the probability law to payoff evaluation.
* `minimumBudgetPMFWithInit_conservation`: proves that spent and remaining budgets sum to the
  initial budget.
* `chargedInitialPMF_success_half`: establishes the one-half minimum-finding guarantee.

## References

* [Dürr and Høyer, 1996][DurrHoyer1996]
* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AmplitudeSearch.InterruptMin
open Qatlib.Concepts.AmplitudeSearch.InterruptMin.CostedLaw

open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.SearchStopping.UnknownCount

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib.Concepts.SearchStopping.GroverSuccess Qatlib.Concepts.SearchStopping.UnknownCount
open scoped ENNReal BigOperators Classical

variable {N : ℕ} {α : Type*} [LinearOrder α]

/-- Every supported successful finite-budget search candidate strictly improves the current
table value and is selected by `checkedUpdate`. -/
theorem minimum_search_success_checkedUpdate (T : Fin N → α) (hN : 0 < N)
    (budget : ℕ) (current candidate : Fin N) (remaining : ℕ)
    (hx : (some candidate, remaining) ∈ (finiteBudgetPMF (by simpa using! hN)
      (strictMarked T current) (ExponentialSizes N)
      (search_exponential_schedule N hN).2.1 0 budget).support) :
    T candidate < T current ∧ checkedUpdate T current candidate = candidate := by
  have hmem := finiteBudgetPMF_success_mem (by simpa using! hN) (strictMarked T current)
    (ExponentialSizes N) (search_exponential_schedule N hN).2.1 0 budget candidate remaining hx
  have hlt : T candidate < T current := by
    simpa only [strictMarked, Finset.mem_filter, Finset.mem_univ, true_and] using! hmem
  exact ⟨hlt, if_pos hlt⟩

/-- The joint probability law of the returned index and remaining budget for recursive minimum
search with an initialization charge [DurrHoyer1996]. -/
noncomputable def minimumBudgetPMFWithInit (T : Fin N → α) (initialization : ℕ)
    (hN : 0 < N) (budget : ℕ) (current : Fin N) : PMF (Fin N × ℕ) :=
  if N = 1 then PMF.pure (current, budget) else
    if initialization ≤ budget then
      (finiteBudgetPMF (by simpa using! hN) (strictMarked T current) (ExponentialSizes N)
        (search_exponential_schedule N hN).2.1 0 (budget - initialization)).bind fun x =>
        match x.1 with
        | none => PMF.pure (current, x.2)
        | some candidate =>
          if _hr : x.2 < budget then
            minimumBudgetPMFWithInit T initialization hN x.2
              (checkedUpdate T current candidate)
          else PMF.pure (current, x.2)
    else PMF.pure (current, budget)
termination_by budget

/-- Every supported outcome has remaining budget at most the initial budget. -/
theorem minimumBudgetPMFWithInit_remaining (T : Fin N → α) (initialization : ℕ)
    (hN : 0 < N) (budget : ℕ) (current : Fin N) (x : Fin N × ℕ)
    (hx : x ∈ (minimumBudgetPMFWithInit T initialization hN budget current).support) :
    x.2 ≤ budget := by
  induction budget using Nat.strong_induction_on generalizing current with
  | h budget ih =>
    rw [minimumBudgetPMFWithInit] at hx
    split_ifs at hx with hsingle hpaid
    · have heq := (PMF.mem_support_pure_iff _ _).mp hx
      simp [heq]
    · obtain ⟨y, hy, hxy⟩ := (PMF.mem_support_bind_iff _ _ x).mp hx
      have hyr := (finiteBudgetPMF_remaining (by simpa using! hN) (strictMarked T current)
        (ExponentialSizes N) (search_exponential_schedule N hN).2.1 0
        (budget - initialization) y hy).1
      have hyB : y.2 ≤ budget := hyr.trans (Nat.sub_le _ _)
      cases ho : y.1 with
      | none =>
        simp only [ho] at hxy
        have heq := (PMF.mem_support_pure_iff _ _).mp hxy
        simpa [heq] using! hyB
      | some candidate =>
        simp only [ho] at hxy
        by_cases hr : y.2 < budget
        · rw [dif_pos hr] at hxy
          exact (ih y.2 hr _ hxy).trans hyB
        · rw [dif_neg hr] at hxy
          have heq := (PMF.mem_support_pure_iff _ _).mp hxy
          simpa [heq] using! hyB
    · have heq := (PMF.mem_support_pure_iff _ _).mp hx
      simp [heq]

/-- Starting from a global minimum leaves the output index equal to the current index in every
supported outcome. -/
theorem minimumBudgetPMFWithInit_minimum_output (T : Fin N → α) (initialization : ℕ)
    (hN : 0 < N) (budget : ℕ) (current : Fin N) (hmin : ∀ j, T current ≤ T j)
    (x : Fin N × ℕ)
    (hx : x ∈ (minimumBudgetPMFWithInit T initialization hN budget current).support) :
    x.1 = current := by
  rw [minimumBudgetPMFWithInit] at hx
  split_ifs at hx with hsingle hpaid
  · exact congrArg Prod.fst ((PMF.mem_support_pure_iff _ _).mp hx)
  · obtain ⟨⟨o, r⟩, ho, hxy⟩ := (PMF.mem_support_bind_iff _ _ x).mp hx
    cases o with
    | none => exact congrArg Prod.fst ((PMF.mem_support_pure_iff _ _).mp hxy)
    | some candidate =>
      have hs := minimum_search_success_checkedUpdate T hN (budget - initialization)
        current candidate r ho
      exact (not_lt_of_ge (hmin candidate) hs.1).elim
  · exact congrArg Prod.fst ((PMF.mem_support_pure_iff _ _).mp hx)

/-- The expectation of a nonnegative terminal payoff under the minimum-search law equals the
extended nonnegative real image of its recursive evaluation. -/
theorem minimumBudgetPMFWithInit_expectation (T : Fin N → α) (initialization : ℕ)
    (hN : 0 < N) (budget : ℕ) (current : Fin N) (payoff : Fin N → ℕ → ℝ)
    (hp : ∀ i r, 0 ≤ payoff i r) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (minimumBudgetPMFWithInit T initialization hN budget current)
      (fun x => ENNReal.ofReal (payoff x.1 x.2)) =
      ENNReal.ofReal (minimumBudgetEvalWithInit T initialization budget current payoff) := by
  induction budget using Nat.strong_induction_on generalizing current with
  | h budget ih =>
    rw [minimumBudgetPMFWithInit, minimumBudgetEvalWithInit]
    split_ifs with hsingle hpaid
    · exact Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure _ _
    · rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
      let call := finiteBudgetPMF (by simpa using! hN) (strictMarked T current)
        (ExponentialSizes N) (search_exponential_schedule N hN).2.1 0 (budget - initialization)
      let s : Fin N → ℕ → ℝ := fun i r => if _hr : r < budget then
        minimumBudgetEvalWithInit T initialization r (checkedUpdate T current i) payoff else 0
      let t : ℕ → ℝ := fun r => payoff current r
      calc
        _ = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation call (fun x => ENNReal.ofReal
            (match x.1 with | some i => s i x.2 | none => t x.2)) := by
          unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
          apply tsum_congr
          rintro ⟨o, r⟩
          by_cases hx : call (o, r) = 0
          · change call (o, r) * _ = call (o, r) * _
            rw [hx, zero_mul, zero_mul]
          · have hmem : (o, r) ∈ call.support := (PMF.mem_support_iff _ _).mpr hx
            have hremaining := finiteBudgetPMF_remaining (by simpa using! hN)
              (strictMarked T current) (ExponentialSizes N)
              (search_exponential_schedule N hN).2.1 0 (budget - initialization) (o, r) hmem
            congr 1
            cases o with
            | none => exact Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure _ _
            | some candidate =>
              have hr : r < budget := (hremaining.2 (by simp)).trans_le (Nat.sub_le _ _)
              have hchecked := minimum_search_success_checkedUpdate T hN (budget - initialization)
                current candidate r hmem
              simp only [dif_pos hr, s, hchecked.2]
              exact ih r hr candidate
        _ = ENNReal.ofReal (FiniteBudgetEval (strictMarked T current) (ExponentialSizes N)
            0 (budget - initialization) s t) := by
          have hs : ∀ i r, 0 ≤ s i r := by
            intro i r
            dsimp only [s]
            split_ifs
            · exact minimumBudgetEvalWithInit_nonneg T initialization hN r _ payoff hp
            · exact le_rfl
          have h := finiteBudgetPMF_expectation (by simpa using! hN) (strictMarked T current)
            (ExponentialSizes N) (search_exponential_schedule N hN).2.1 0
            (budget - initialization) s t hs (fun r => hp current r)
          convert! h using 1
          congr 1
          funext x
          rcases x with ⟨o, r⟩
          cases o <;> rfl
        _ = _ := by congr 1
    · exact Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure _ _

/-- Event probability under the minimum-search law equals the extended nonnegative real image of
the corresponding indicator evaluation. -/
theorem minimumBudgetPMFWithInit_event (T : Fin N → α) (initialization : ℕ)
    (hN : 0 < N) (budget : ℕ) (current : Fin N) (E : Fin N × ℕ → Prop) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (minimumBudgetPMFWithInit T initialization hN budget current) E =
      ENNReal.ofReal (minimumBudgetEvalWithInit T initialization budget current
        (fun i r => if E (i, r) then 1 else 0)) := by
  convert! minimumBudgetPMFWithInit_expectation T initialization hN budget current
    (fun i r => if E (i, r) then 1 else 0)
    (fun _ _ => by (try dsimp only); split_ifs <;> norm_num) using 1
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
  congr 1
  funext x
  split_ifs <;> simp

/-- The costed minimum-search law obtained by replacing remaining budget with spent budget
`budget - remaining`. -/
noncomputable def minimumBudgetCostedLawWithInit (T : Fin N → α) (initialization : ℕ)
    (hN : 0 < N) (budget : ℕ) (current : Fin N) : CostedLaw (Fin N) :=
  (minimumBudgetPMFWithInit T initialization hN budget current).map
    (fun x => (x.1, budget - x.2))

/-- The spent cost in the minimum-search law is bounded by the initial budget. -/
theorem minimumBudgetCostedLawWithInit_bounded (T : Fin N → α) (initialization : ℕ)
    (hN : 0 < N) (budget : ℕ) (current : Fin N) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.BoundedBy (minimumBudgetCostedLawWithInit T initialization hN budget current) budget := by
  intro x hx
  obtain ⟨y, _, rfl⟩ := (PMF.mem_support_map_iff _ _ x).mp hx
  exact Nat.sub_le _ _

/-- For every supported outcome, spent budget plus remaining budget equals the initial budget. -/
theorem minimumBudgetPMFWithInit_conservation (T : Fin N → α) (initialization : ℕ)
    (hN : 0 < N) (budget : ℕ) (current : Fin N) (x : Fin N × ℕ)
    (hx : x ∈ (minimumBudgetPMFWithInit T initialization hN budget current).support) :
    (budget - x.2) + x.2 = budget :=
  Nat.sub_add_cancel (minimumBudgetPMFWithInit_remaining T initialization hN budget current x hx)

/-- The joint output-index and remaining-budget law obtained by sampling the initial index and
using initialization charge `initCharge N`. -/
noncomputable def chargedInitialPMF (T : Fin N → α) (hN : 0 < N) (budget : ℕ) :
    PMF (Fin N × ℕ) :=
  (iterationPMF N hN).bind (minimumBudgetPMFWithInit T (initCharge N) hN budget)

/-- The probability that `chargedInitialPMF` returns a global minimum equals `ENNReal.ofReal` of
`chargedInitialSuccess`. -/
theorem chargedInitialPMF_success (T : Fin N → α) (hN : 0 < N) (budget : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (chargedInitialPMF T hN budget) (fun x => ∀ j, T x.1 ≤ T j) =
      ENNReal.ofReal (chargedInitialSuccess T budget) := by
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event chargedInitialPMF
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
  calc
    _ = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (iterationPMF N hN) (fun current =>
        ENNReal.ofReal (minimumBudgetSuccessWithInit T (initCharge N) budget current)) := by
      congr 1
      funext current
      convert! minimumBudgetPMFWithInit_event T (initCharge N) hN budget current
        (fun x => ∀ j, T x.1 ≤ T j) using 1
      congr 1
      unfold minimumBudgetSuccessWithInit
      apply minimumBudgetEvalWithInit_congr
      intro i r _
      by_cases hm : ∀ j, T i ≤ T j <;> simp [hm]
    _ = ENNReal.ofReal (∑ current : Fin N, (iterationPMF N hN current).toReal *
        minimumBudgetSuccessWithInit T (initCharge N) budget current) :=
      Qatlib.Concepts.AmplitudeSearch.InterruptMin.CostedLaw.expectation_ofReal_fintype _ _ (fun current =>
        (minimumBudgetSuccessWithInit_bounds T (initCharge N) hN budget current).1)
    _ = _ := by
      congr 1
      simp_rw [iterationPMF_toReal]
      rw [← Finset.mul_sum]
      unfold chargedInitialSuccess
      ring

/-- At budget `chargedBudget N`, the charged initial minimum-search law returns a global minimum
with probability at least one half. -/
theorem chargedInitialPMF_success_half (T : Fin N → α) (hN : 0 < N) :
    (1 / 2 : ℝ≥0∞) ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (chargedInitialPMF T hN (chargedBudget N))
      (fun x => ∀ j, T x.1 ≤ T j) := by
  rw [chargedInitialPMF_success]
  have h := ENNReal.ofReal_le_ofReal (charged_initial_success_half T hN)
  simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
    ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using! h

end Qatlib.Concepts.AmplitudeSearch.Amplification
