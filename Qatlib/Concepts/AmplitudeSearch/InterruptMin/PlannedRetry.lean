/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.RealMass
import Mathlib.Data.PNat.Basic

/-!
# Budgeted retries with sampled plans

This module defines `PlannedRetry`, whose state-dependent plans have positive costs and optional
outputs. Its execution law checks whether a sampled plan fits the budget, retries failures, and
returns either a successful output or a timeout with the remaining budget.

The finite evaluator, event formulas, and cost bounds provide a general probability interface
for randomized search retries [BoyerEtAl1998].

## Main statements

* `PlannedRetry`: A retry scheme with state-dependent sampled plans, positive plan costs,
  optional outputs, and a state update after failure.
* `run_remaining`: Every supported run leaves at most the initial budget, and a successful run
  leaves strictly less.
* `run_expectation`: For nonnegative payoffs, expectation under the run law equals the extended
  nonnegative embedding of the real evaluator.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AmplitudeSearch.InterruptMin.CostedLaw
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.InterruptMin
open scoped ENNReal BigOperators Classical

universe u v w

/-- A retry scheme with state-dependent sampled plans, positive plan costs, optional outputs,
and a state update after failure. -/
structure PlannedRetry (State : Type u) (Output : Type v) where
  Plan : State → Type w
  choose : (s : State) → PMF (Plan s)
  cost : (s : State) → Plan s → ℕ+
  perform : (s : State) → Plan s → PMF (Option Output)
  retry : (s : State) → Plan s → State

namespace PlannedRetry
variable {State : Type u} {Output : Type v}

/-- The budgeted retry law returning an optional output and remaining budget, with timeout when
a sampled plan does not fit. -/
noncomputable def run (K : PlannedRetry State Output) (budget : ℕ) (s : State) :
    PMF (Option Output × ℕ) :=
  (K.choose s).bind fun p =>
    if _hc : (K.cost s p : ℕ) ≤ budget then
      (K.perform s p).bind fun o =>
        match o with
        | some a => PMF.pure (some a, budget - K.cost s p)
        | none => K.run (budget - K.cost s p) (K.retry s p)
    else PMF.pure (none, budget)
termination_by budget
decreasing_by
  exact Nat.sub_lt (lt_of_lt_of_le (K.cost s p).pos _hc) (K.cost s p).pos

/-- Every supported run leaves at most the initial budget, and a successful run leaves strictly
less. -/
theorem run_remaining (K : PlannedRetry State Output) (budget : ℕ) (s : State)
    (x : Option Output × ℕ) (hx : x ∈ (K.run budget s).support) :
    x.2 ≤ budget ∧ (x.1 ≠ none → x.2 < budget) := by
  induction budget using Nat.strong_induction_on generalizing s with
  | h budget ih =>
    rw [run] at hx
    obtain ⟨p, _, hp⟩ := (PMF.mem_support_bind_iff _ _ x).mp hx
    by_cases hc : (K.cost s p : ℕ) ≤ budget
    · rw [dif_pos hc] at hp
      obtain ⟨o, _, ho⟩ := (PMF.mem_support_bind_iff _ _ x).mp hp
      have hlt : budget - (K.cost s p : ℕ) < budget :=
        Nat.sub_lt (lt_of_lt_of_le (K.cost s p).pos hc) (K.cost s p).pos
      have hr : x.2 ≤ budget - (K.cost s p : ℕ) := by
        cases o with
        | none => exact (ih _ hlt _ ho).1
        | some a =>
          have heq := (PMF.mem_support_pure_iff _ _).mp ho
          simp only [heq, le_refl]
      exact ⟨hr.trans hlt.le, fun _ => hr.trans_lt hlt⟩
    · rw [dif_neg hc] at hp
      have heq := (PMF.mem_support_pure_iff _ _).mp hp
      simp [heq]

/-- A zero-budget run returns timeout with zero remaining budget. -/
@[simp] theorem run_zero (K : PlannedRetry State Output) (s : State) :
    K.run 0 s = PMF.pure (none, 0) := by
  rw [run]
  have h (p : K.Plan s) : ¬ (K.cost s p : ℕ) ≤ 0 := Nat.not_le.mpr (K.cost s p).pos
  simp only [h, dite_false]
  exact PMF.bind_const _ _

/-- The run law paired with consumed cost, computed as initial budget minus remaining budget. -/
noncomputable def costedRun (K : PlannedRetry State Output) (budget : ℕ) (s : State) :
    CostedLaw (Option Output) :=
  (K.run budget s).map (fun x => (x.1, budget - x.2))

/-- The costed run is bounded by the initial budget. -/
theorem costedRun_bounded (K : PlannedRetry State Output) (budget : ℕ) (s : State) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.BoundedBy (K.costedRun budget s) budget := by
  intro x hx
  obtain ⟨y, _, rfl⟩ := (PMF.mem_support_map_iff _ _ x).mp hx
  exact Nat.sub_le _ _

/-- For every supported run, consumed cost plus remaining budget equals the initial budget. -/
theorem run_budget_conservation (K : PlannedRetry State Output) (budget : ℕ) (s : State)
    (x : Option Output × ℕ) (hx : x ∈ (K.run budget s).support) :
    (budget - x.2) + x.2 = budget := Nat.sub_add_cancel (K.run_remaining budget s x hx).1

section Finite

/-- The real recursive payoff evaluator for finite plan and output types, with separate success
and timeout payoffs. -/
noncomputable def eval (K : PlannedRetry State Output)
    [∀ s, Fintype (K.Plan s)] [Fintype Output] (budget : ℕ) (s : State)
    (onSuccess : Output → ℕ → ℝ) (onTimeout : ℕ → ℝ) : ℝ :=
  ∑ p : K.Plan s, (K.choose s p).toReal *
    (if _hc : (K.cost s p : ℕ) ≤ budget then
      ∑ o : Option Output, (K.perform s p o).toReal *
        (match o with
        | some a => onSuccess a (budget - K.cost s p)
        | none => K.eval (budget - K.cost s p) (K.retry s p) onSuccess onTimeout)
    else onTimeout budget)
termination_by budget
decreasing_by
  exact Nat.sub_lt (lt_of_lt_of_le (K.cost s p).pos _hc) (K.cost s p).pos

variable (K : PlannedRetry State Output) [∀ s, Fintype (K.Plan s)] [Fintype Output]

/-- The retry evaluator is nonnegative when success and timeout payoffs are nonnegative. -/
theorem eval_nonneg (budget : ℕ) (s : State)
    (onSuccess : Output → ℕ → ℝ) (onTimeout : ℕ → ℝ)
    (hs : ∀ a r, 0 ≤ onSuccess a r) (ht : ∀ r, 0 ≤ onTimeout r) :
    0 ≤ K.eval budget s onSuccess onTimeout := by
  induction budget using Nat.strong_induction_on generalizing s with
  | h budget ih =>
    rw [eval]
    apply Finset.sum_nonneg
    intro p _
    apply mul_nonneg ENNReal.toReal_nonneg
    split_ifs with hc
    · apply Finset.sum_nonneg
      intro o _
      apply mul_nonneg ENNReal.toReal_nonneg
      cases o with
      | some a => exact hs a _
      | none => exact ih _ (Nat.sub_lt (lt_of_lt_of_le (K.cost s p).pos hc)
          (K.cost s p).pos) _
    · exact ht budget

/-- The retry evaluator preserves pointwise order of success and timeout payoffs. -/
theorem eval_mono (budget : ℕ) (s : State)
    (f g : Output → ℕ → ℝ) (t u : ℕ → ℝ)
    (hfg : ∀ a r, f a r ≤ g a r) (htu : ∀ r, t r ≤ u r) :
    K.eval budget s f t ≤ K.eval budget s g u := by
  induction budget using Nat.strong_induction_on generalizing s with
  | h budget ih =>
    rw [eval, eval]
    apply Finset.sum_le_sum
    intro p _
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    split_ifs with hc
    · apply Finset.sum_le_sum
      intro o _
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      cases o with
      | some a => exact hfg a _
      | none => exact ih _ (Nat.sub_lt (lt_of_lt_of_le (K.cost s p).pos hc)
          (K.cost s p).pos) _
    · exact htu budget

/-- Expands the evaluator as a joint sum over sampled plans and optional attempt outputs. -/
theorem eval_eq_joint_sum (budget : ℕ) (s : State)
    (onSuccess : Output → ℕ → ℝ) (onTimeout : ℕ → ℝ) :
    K.eval budget s onSuccess onTimeout =
      ∑ p : K.Plan s, ∑ o : Option Output,
        ((K.choose s p).toReal * (K.perform s p o).toReal) *
          (if _hc : (K.cost s p : ℕ) ≤ budget then
            match o with
            | some a => onSuccess a (budget - K.cost s p)
            | none => K.eval (budget - K.cost s p) (K.retry s p) onSuccess onTimeout
          else onTimeout budget) := by
  rw [eval]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hc : (K.cost s p : ℕ) ≤ budget
  · simp only [dif_pos hc, Finset.mul_sum, mul_assoc]
  · simp only [dif_neg hc]
    have hsum : (∑ o : Option Output, (K.perform s p o).toReal) = 1 := by
      rw [← ENNReal.toReal_sum (fun o _ => (K.perform s p).apply_ne_top o)]
      have hn : (∑ o : Option Output, K.perform s p o) = 1 := by
        simpa only [tsum_fintype] using (K.perform s p).tsum_coe
      rw [hn, ENNReal.toReal_one]
    rw [← Finset.sum_mul, ← Finset.mul_sum, hsum, mul_one]

/-- For nonnegative payoffs, expectation under the run law equals the extended nonnegative
embedding of the real evaluator. -/
theorem run_expectation (budget : ℕ) (s : State)
    (onSuccess : Output → ℕ → ℝ) (onTimeout : ℕ → ℝ)
    (hs : ∀ a r, 0 ≤ onSuccess a r) (ht : ∀ r, 0 ≤ onTimeout r) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (K.run budget s)
      (fun x => ENNReal.ofReal (match x.1 with
        | some a => onSuccess a x.2
        | none => onTimeout x.2)) = ENNReal.ofReal (K.eval budget s onSuccess onTimeout) := by
  induction budget using Nat.strong_induction_on generalizing s with
  | h budget ih =>
    let payoff : Option Output × ℕ → ℝ≥0∞ := fun x => ENNReal.ofReal (match x.1 with
      | some a => onSuccess a x.2
      | none => onTimeout x.2)
    rw [run, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind, eval]
    have heach (p : K.Plan s) :
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
          (if _hc : (K.cost s p : ℕ) ≤ budget then
            (K.perform s p).bind fun o => match o with
              | some a => PMF.pure (some a, budget - K.cost s p)
              | none => K.run (budget - K.cost s p) (K.retry s p)
          else PMF.pure (none, budget)) payoff =
        ENNReal.ofReal (if _hc : (K.cost s p : ℕ) ≤ budget then
          ∑ o : Option Output, (K.perform s p o).toReal * (match o with
            | some a => onSuccess a (budget - K.cost s p)
            | none => K.eval (budget - K.cost s p) (K.retry s p) onSuccess onTimeout)
          else onTimeout budget) := by
      by_cases hc : (K.cost s p : ℕ) ≤ budget
      · simp only [dif_pos hc, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
        have he (o : Option Output) :
            Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
              (match o with
              | some a => PMF.pure (some a, budget - K.cost s p)
              | none => K.run (budget - K.cost s p) (K.retry s p)) payoff =
            ENNReal.ofReal (match o with
              | some a => onSuccess a (budget - K.cost s p)
              | none => K.eval (budget - K.cost s p) (K.retry s p) onSuccess onTimeout) := by
          cases o with
          | some a => exact Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure _ _
          | none => exact ih _ (Nat.sub_lt (lt_of_lt_of_le (K.cost s p).pos hc)
              (K.cost s p).pos) _
        simp_rw [he]
        apply Qatlib.Concepts.AmplitudeSearch.InterruptMin.CostedLaw.expectation_ofReal_fintype
        intro o
        cases o with
        | some a => exact hs a _
        | none => exact K.eval_nonneg _ _ _ _ hs ht
      · simp only [dif_neg hc, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure,
          payoff]
    change Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (K.choose s)
        (fun p => _) = _
    calc
      _ = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (K.choose s) (fun p => ENNReal.ofReal
          (if _hc : (K.cost s p : ℕ) ≤ budget then
            ∑ o : Option Output, (K.perform s p o).toReal * (match o with
              | some a => onSuccess a (budget - K.cost s p)
              | none => K.eval (budget - K.cost s p) (K.retry s p) onSuccess onTimeout)
            else onTimeout budget)) := by
        congr 1
        funext p
        exact heach p
      _ = _ := by
        apply Qatlib.Concepts.AmplitudeSearch.InterruptMin.CostedLaw.expectation_ofReal_fintype
        intro p
        split_ifs with hc
        · apply Finset.sum_nonneg
          intro o _
          apply mul_nonneg ENNReal.toReal_nonneg
          cases o with
          | some a => exact hs a _
          | none => exact K.eval_nonneg _ _ _ _ hs ht
        · exact ht budget

/-- The probability of a run event equals the evaluator applied to its success and timeout
indicators. -/
theorem run_event (budget : ℕ) (s : State) (E : Option Output × ℕ → Prop) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (K.run budget s) E = ENNReal.ofReal
      (K.eval budget s (fun a r => if E (some a, r) then 1 else 0)
        (fun r => if E (none, r) then 1 else 0)) := by
  convert K.run_expectation budget s
    (fun a r => if E (some a, r) then 1 else 0)
    (fun r => if E (none, r) then 1 else 0)
    (fun _ _ => by (try dsimp only); split_ifs <;> norm_num)
    (fun _ => by (try dsimp only); split_ifs <;> norm_num) using 1
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
  congr 1
  funext x
  rcases x with ⟨o, r⟩
  cases o <;> (try dsimp only) <;> split_ifs <;> simp

/-- The mass of a single run result equals the evaluator applied to the corresponding singleton
indicators. -/
theorem run_apply [DecidableEq Output] (budget : ℕ) (s : State) (x : Option Output × ℕ) :
    K.run budget s x = ENNReal.ofReal
      (K.eval budget s (fun a r => if (some a, r) = x then 1 else 0)
        (fun r => if (none, r) = x then 1 else 0)) := by
  have h := K.run_event budget s (fun y => y = x)
  convert h using 1
  · simp [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation]
  · congr 2
    · funext a r
      by_cases hx : (some a, r) = x <;> simp [hx]
    · funext r
      by_cases hx : (none, r) = x <;> simp [hx]

end Finite
end PlannedRetry
end Qatlib.Concepts.AmplitudeSearch.InterruptMin
