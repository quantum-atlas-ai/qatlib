/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.SearchProbability
import Qatlib.Concepts.AmplitudeSearch.InterruptMin.SearchBudgetEval
import Qatlib.Concepts.AmplitudeSearch.InterruptMin.PlannedRetry

/-!
# Probability semantics of finite-budget search

This module instantiates `PlannedRetry` with randomized checked search attempts. It constructs
`finiteBudgetPMF` and `finiteBudgetCostedLaw`, proves their evaluator formulas, and shows that
supported successful outputs are marked and consume positive budget.

The construction gives probability semantics to finite-budget randomized search [BoyerEtAl1998].

## Main statements

* `finiteBudgetPMF_expectation`: For nonnegative success and timeout payoffs, expectation under
  `finiteBudgetPMF` equals the embedded finite-budget evaluator.
* `finiteBudgetPMF_success_mem`: Every supported successful finite-budget search output belongs
  to the marked set.
* `finiteBudgetCostedLaw_bounded`: The consumed cost of finite-budget search is bounded by its
  initial budget.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.SearchStopping.UnknownCount
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AmplitudeSearch.InterruptMin.PlannedRetry

open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.LinearLearning.ConcisePipeline

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.InterruptMin
open Qatlib
open scoped ENNReal BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The planned retry scheme that uniformly samples an iteration count, charges that count plus
one, performs a checked search attempt, and advances the stage on failure. -/
noncomputable def searchPlan (hN : 0 < Fintype.card I) (A : Finset I)
    (sizes : ℕ → ℕ) (hsizes : ∀ k, 0 < sizes k) : PlannedRetry ℕ I where
  Plan k := Fin (sizes k)
  choose k := iterationPMF (sizes k) (hsizes k)
  cost _ j := ⟨j.val + 1, Nat.succ_pos _⟩
  perform _ j := checkedOutcomePMF hN A j.val
  retry k _ := k + 1

instance searchPlan_planFintype (hN : 0 < Fintype.card I) (A : Finset I)
    (sizes : ℕ → ℕ) (hsizes : ∀ k, 0 < sizes k) :
    ∀ k, Fintype ((searchPlan hN A sizes hsizes).Plan k) :=
  fun k => inferInstanceAs (Fintype (Fin (sizes k)))

/-- The evaluator of `searchPlan` equals `FiniteBudgetEval`. -/
theorem search_planned_eval_eq (hN : 0 < Fintype.card I) (A : Finset I)
    (sizes : ℕ → ℕ) (hsizes : ∀ k, 0 < sizes k) (stage budget : ℕ)
    (s : I → ℕ → ℝ) (t : ℕ → ℝ) :
    (searchPlan hN A sizes hsizes).eval budget stage s t =
      FiniteBudgetEval A sizes stage budget s t := by
  induction budget using Nat.strong_induction_on generalizing stage with
  | h budget ih =>
    rw [PlannedRetry.eval_eq_joint_sum, FiniteBudgetEval, Fintype.sum_prod_type]
    change (∑ j : Fin (sizes stage), ∑ o : Option I,
      ((iterationPMF (sizes stage) (hsizes stage) j).toReal *
        (checkedOutcomePMF hN A j.val o).toReal) *
        (if _hc : j.val + 1 ≤ budget then
          match o with
          | some i => s i (budget - (j.val + 1))
          | none => (searchPlan hN A sizes hsizes).eval (budget - (j.val + 1))
              (stage + 1) s t
        else t budget)) = _
    simp_rw [search_attempt_factor]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro o _
    congr 1
    by_cases hc : j.val + 1 ≤ budget
    · simp only [dif_pos hc]
      cases o with
      | some i => rfl
      | none => exact ih _ (search_budget_progress _ _ hc) (stage + 1)
    · simp only [dif_neg hc]

/-- The finite-budget search law on optional outputs and remaining budgets, obtained from
`searchPlan`. -/
noncomputable def finiteBudgetPMF (hN : 0 < Fintype.card I) (A : Finset I)
    (sizes : ℕ → ℕ) (hsizes : ∀ k, 0 < sizes k) (stage budget : ℕ) :
    PMF (Option I × ℕ) := (searchPlan hN A sizes hsizes).run budget stage

/-- For nonnegative success and timeout payoffs, expectation under `finiteBudgetPMF` equals the
embedded finite-budget evaluator. -/
theorem finiteBudgetPMF_expectation (hN : 0 < Fintype.card I) (A : Finset I)
    (sizes : ℕ → ℕ) (hsizes : ∀ k, 0 < sizes k) (stage budget : ℕ)
    (s : I → ℕ → ℝ) (t : ℕ → ℝ) (hs : ∀ i r, 0 ≤ s i r) (ht : ∀ r, 0 ≤ t r) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (finiteBudgetPMF hN A sizes hsizes stage budget)
      (fun x => ENNReal.ofReal (match x.1 with | some i => s i x.2 | none => t x.2)) =
      ENNReal.ofReal (FiniteBudgetEval A sizes stage budget s t) := by
  rw [← search_planned_eval_eq hN A sizes hsizes stage budget s t]
  exact PlannedRetry.run_expectation _ _ _ s t hs ht

/-- The probability of a finite-budget search event equals evaluation of its success and timeout
indicators. -/
theorem finiteBudgetPMF_event (hN : 0 < Fintype.card I) (A : Finset I)
    (sizes : ℕ → ℕ) (hsizes : ∀ k, 0 < sizes k) (stage budget : ℕ)
    (E : Option I × ℕ → Prop) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (finiteBudgetPMF hN A sizes hsizes stage budget) E =
      ENNReal.ofReal (FiniteBudgetEval A sizes stage budget
        (fun i r => if E (some i, r) then 1 else 0)
        (fun r => if E (none, r) then 1 else 0)) := by
  rw [← search_planned_eval_eq hN A sizes hsizes stage budget]
  exact PlannedRetry.run_event _ _ _ E

/-- The mass of a finite-budget search result equals evaluation of its singleton indicators. -/
theorem finiteBudgetPMF_apply (hN : 0 < Fintype.card I) (A : Finset I)
    (sizes : ℕ → ℕ) (hsizes : ∀ k, 0 < sizes k) (stage budget : ℕ) (x : Option I × ℕ) :
    finiteBudgetPMF hN A sizes hsizes stage budget x =
      ENNReal.ofReal (FiniteBudgetEval A sizes stage budget
        (fun i r => if (some i, r) = x then 1 else 0)
        (fun r => if (none, r) = x then 1 else 0)) := by
  rw [← search_planned_eval_eq hN A sizes hsizes stage budget]
  exact PlannedRetry.run_apply _ _ _ x

/-- The finite-budget search law paired with consumed query cost. -/
noncomputable def finiteBudgetCostedLaw (hN : 0 < Fintype.card I) (A : Finset I)
    (sizes : ℕ → ℕ) (hsizes : ∀ k, 0 < sizes k) (stage budget : ℕ) : CostedLaw (Option I) :=
  (searchPlan hN A sizes hsizes).costedRun budget stage

/-- The consumed cost of finite-budget search is bounded by its initial budget. -/
theorem finiteBudgetCostedLaw_bounded (hN : 0 < Fintype.card I) (A : Finset I)
    (sizes : ℕ → ℕ) (hsizes : ∀ k, 0 < sizes k) (stage budget : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.BoundedBy (finiteBudgetCostedLaw hN A sizes hsizes stage budget) budget :=
  PlannedRetry.costedRun_bounded _ _ _

/-- Every supported finite-budget result leaves at most the initial budget, and every successful
result leaves strictly less. -/
theorem finiteBudgetPMF_remaining (hN : 0 < Fintype.card I) (A : Finset I)
    (sizes : ℕ → ℕ) (hsizes : ∀ k, 0 < sizes k) (stage budget : ℕ)
    (x : Option I × ℕ) (hx : x ∈ (finiteBudgetPMF hN A sizes hsizes stage budget).support) :
    x.2 ≤ budget ∧ (x.1 ≠ none → x.2 < budget) :=
  PlannedRetry.run_remaining _ _ _ x hx

/-- Every supported successful finite-budget search output belongs to the marked set. -/
theorem finiteBudgetPMF_success_mem (hN : 0 < Fintype.card I) (A : Finset I)
    (sizes : ℕ → ℕ) (hsizes : ∀ k, 0 < sizes k) (stage budget : ℕ) (i : I) (r : ℕ)
    (hx : (some i, r) ∈ (finiteBudgetPMF hN A sizes hsizes stage budget).support) :
    i ∈ A := by
  change (some i, r) ∈ ((searchPlan hN A sizes hsizes).run budget stage).support at hx
  induction budget using Nat.strong_induction_on generalizing stage with
  | h budget ih =>
    rw [PlannedRetry.run] at hx
    obtain ⟨j, _, hj⟩ := (PMF.mem_support_bind_iff _ _ (some i, r)).mp hx
    by_cases hc : ((searchPlan hN A sizes hsizes).cost stage j : ℕ) ≤ budget
    · rw [dif_pos hc] at hj
      obtain ⟨o, ho, hx⟩ := (PMF.mem_support_bind_iff _ _ (some i, r)).mp hj
      cases o with
      | none => exact ih _ (search_budget_progress _ _ hc) (stage + 1) hx
      | some a =>
        have heq := (PMF.mem_support_pure_iff _ _).mp hx
        have hai : i = a := by simpa using congrArg (fun x => x.1) heq
        subst a
        by_contra hi
        have hz : checkedOutcomePMF hN A j.val (some i) = 0 := by
          change ENNReal.ofReal (CheckedOutputMass A j.val i) = 0
          rw [(search_checked_attempt hN A j.val).2.1 i, if_neg hi, ENNReal.ofReal_zero]
        exact (PMF.mem_support_iff _ _).mp ho hz
    · rw [dif_neg hc] at hj
      have heq := (PMF.mem_support_pure_iff _ _).mp hj
      simp at heq

/-- The finite-budget evaluator preserves pointwise order of success and timeout payoffs. -/
theorem search_finite_budget_eval_mono (hN : 0 < Fintype.card I) (A : Finset I)
    (sizes : ℕ → ℕ) (hsizes : ∀ k, 0 < sizes k) (stage budget : ℕ)
    (f g : I → ℕ → ℝ) (s t : ℕ → ℝ)
    (hfg : ∀ i r, f i r ≤ g i r) (hst : ∀ r, s r ≤ t r) :
    FiniteBudgetEval A sizes stage budget f s ≤ FiniteBudgetEval A sizes stage budget g t := by
  rw [← search_planned_eval_eq hN A sizes hsizes stage budget f s,
    ← search_planned_eval_eq hN A sizes hsizes stage budget g t]
  exact PlannedRetry.eval_mono _ _ _ f g s t hfg hst

end Qatlib.Concepts.AmplitudeSearch.InterruptMin
