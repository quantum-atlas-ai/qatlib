/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.InterruptedCallBudget
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AmplitudeSearch.InterruptMin.CostedLaw

open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.SearchStopping.UnknownCount

set_option autoImplicit false
namespace Qatlib.Concepts.AmplitudeSearch.InterruptMin
open Qatlib.Concepts.SearchStopping.GroverSuccess Qatlib.Concepts.SearchStopping.UnknownCount
open scoped ENNReal BigOperators Classical
variable {I : Type} [Fintype I] [DecidableEq I]

theorem interrupted_eval_nonneg (hN : 0 < Fintype.card I) (A : Finset I)
    (sizes : ℕ → ℕ) (hsizes : ∀ k, 0 < sizes k) (stage budget : ℕ)
    (s : I → ℕ → ℝ) (hs : ∀ i r, 0 ≤ s i r) :
    0 ≤ interruptedBudgetEval A sizes stage budget s := by
  induction budget using Nat.strong_induction_on generalizing stage with
  | h budget ih =>
    rw [interruptedBudgetEval]
    apply Finset.sum_nonneg
    intro x _
    apply mul_nonneg ((search_joint_attempt_law hN A (sizes stage) (hsizes stage)).1 x)
    by_cases hc : x.1.val + 1 ≤ budget
    · simp only [dif_pos hc]
      cases x.2 with
      | some i => exact hs i _
      | none => exact ih _ (search_budget_progress _ _ hc) (stage + 1)
    · simp only [dif_neg hc]
      exact Finset.sum_nonneg fun i _ => mul_nonneg (partialObsMass_nonneg _ _ _ _) (hs i 0)

theorem interrupted_eval_one (hN : 0 < Fintype.card I) (A : Finset I)
    (sizes : ℕ → ℕ) (hsizes : ∀ k, 0 < sizes k) (stage budget : ℕ) :
    interruptedBudgetEval A sizes stage budget (fun _ _ => 1) = 1 := by
  induction budget using Nat.strong_induction_on generalizing stage with
  | h budget ih =>
    rw [interruptedBudgetEval]
    calc
      _ = ∑ x : Fin (sizes stage) × Option I, AttemptMass A (sizes stage) x := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hc : x.1.val + 1 ≤ budget
        · simp only [dif_pos hc]
          cases x.2 with
          | some i => simp
          | none => rw [ih _ (search_budget_progress _ _ hc) (stage + 1)]; simp
        · simp only [dif_neg hc, mul_one]
          have hm : (∑ i : I, partialObsMass A x.1.val budget i) = 1 := by
            simpa only [tsum_fintype] using (partialObsMass_sum_one hN A x.1.val budget).tsum_eq
          rw [hm, mul_one]
      _ = 1 := (search_joint_attempt_law hN A (sizes stage) (hsizes stage)).2.1

theorem interrupted_eval_mono (hN : 0 < Fintype.card I) (A : Finset I)
    (sizes : ℕ → ℕ) (hsizes : ∀ k, 0 < sizes k) (stage budget : ℕ)
    (f g : I → ℕ → ℝ) (hfg : ∀ i r, f i r ≤ g i r) :
    interruptedBudgetEval A sizes stage budget f ≤ interruptedBudgetEval A sizes stage budget g := by
  induction budget using Nat.strong_induction_on generalizing stage with
  | h budget ih =>
    conv_lhs => rw [interruptedBudgetEval]
    conv_rhs => rw [interruptedBudgetEval]
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left _
      ((search_joint_attempt_law hN A (sizes stage) (hsizes stage)).1 x)
    by_cases hc : x.1.val + 1 ≤ budget
    · simp only [dif_pos hc]
      cases x.2 with
      | some i => exact hfg i _
      | none => exact ih _ (search_budget_progress _ _ hc) (stage + 1)
    · simp only [dif_neg hc]
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hfg i 0)
        (partialObsMass_nonneg _ _ _ _)

theorem interrupted_call_remaining (hN : 0 < Fintype.card I) (A : Finset I)
    (sizes : ℕ → ℕ) (hsizes : ∀ k, 0 < sizes k) (stage budget : ℕ)
    (x : I × ℕ) (hx : x ∈ (interruptedBudgetPMF hN A sizes hsizes stage budget).support) :
    x.2 ≤ budget := by
  induction budget using Nat.strong_induction_on generalizing stage with
  | h budget ih =>
    rw [interruptedBudgetPMF] at hx
    obtain ⟨j, _, hj⟩ := (PMF.mem_support_bind_iff _ _ x).mp hx
    by_cases hc : j.val + 1 ≤ budget
    · rw [dif_pos hc] at hj
      obtain ⟨o, _, ho⟩ := (PMF.mem_support_bind_iff _ _ x).mp hj
      cases o with
      | some i =>
        have heq := (PMF.mem_support_pure_iff _ _).mp ho
        simp [heq]
      | none => exact (ih _ (search_budget_progress _ _ hc) (stage + 1) ho).trans (Nat.sub_le _ _)
    · rw [dif_neg hc] at hj
      obtain ⟨i, _, hi⟩ := (PMF.mem_support_bind_iff _ _ x).mp hj
      have heq := (PMF.mem_support_pure_iff _ _).mp hi
      simp [heq]

theorem interrupted_call_expectation (hN : 0 < Fintype.card I) (A : Finset I)
    (sizes : ℕ → ℕ) (hsizes : ∀ k, 0 < sizes k) (stage budget : ℕ)
    (s : I → ℕ → ℝ) (hs : ∀ i r, 0 ≤ s i r) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (interruptedBudgetPMF hN A sizes hsizes stage budget)
      (fun x => ENNReal.ofReal (s x.1 x.2)) =
      ENNReal.ofReal (interruptedBudgetEval A sizes stage budget s) := by
  induction budget using Nat.strong_induction_on generalizing stage with
  | h budget ih =>
    rw [interruptedBudgetPMF, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
    let w : Fin (sizes stage) → Option I → ℝ := fun j o =>
      if _hc : j.val + 1 ≤ budget then
        match o with
        | some i => s i (budget - (j.val + 1))
        | none => interruptedBudgetEval A sizes (stage + 1) (budget - (j.val + 1)) s
      else ∑ i : I, partialObsMass A j.val budget i * s i 0
    have hw : ∀ j o, 0 ≤ w j o := by
      intro j o
      dsimp only [w]
      split_ifs with hc
      · cases o with
        | some i => exact hs i _
        | none => exact interrupted_eval_nonneg hN A sizes hsizes _ _ s hs
      · exact Finset.sum_nonneg fun i _ => mul_nonneg (partialObsMass_nonneg _ _ _ _) (hs i 0)
    have heach (j : Fin (sizes stage)) :
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
          (if _hc : j.val + 1 ≤ budget then
            (checkedOutcomePMF hN A j.val).bind fun o => match o with
              | some i => PMF.pure (i, budget - (j.val + 1))
              | none => interruptedBudgetPMF hN A sizes hsizes (stage + 1) (budget - (j.val + 1))
          else (partialObsPMF hN A j.val budget).bind fun i => PMF.pure (i, 0))
          (fun x => ENNReal.ofReal (s x.1 x.2)) =
        ENNReal.ofReal (∑ o : Option I, (checkedOutcomePMF hN A j.val o).toReal * w j o) := by
      by_cases hc : j.val + 1 ≤ budget
      · simp only [dif_pos hc, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
        have he (o : Option I) :
            Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (match o with
              | some i => PMF.pure (i, budget - (j.val + 1))
              | none => interruptedBudgetPMF hN A sizes hsizes (stage + 1) (budget - (j.val + 1)))
              (fun x => ENNReal.ofReal (s x.1 x.2)) = ENNReal.ofReal (w j o) := by
          cases o with
          | some i =>
            simpa only [w, dif_pos hc] using (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure
              (i, budget - (j.val + 1)) (fun x => ENNReal.ofReal (s x.1 x.2)))
          | none => simpa only [w, dif_pos hc] using ih _ (search_budget_progress _ _ hc) (stage + 1)
        simp_rw [he]
        exact Qatlib.Concepts.AmplitudeSearch.InterruptMin.CostedLaw.expectation_ofReal_fintype _ _ (hw j)
      · simp only [dif_neg hc, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure]
        rw [Qatlib.Concepts.AmplitudeSearch.InterruptMin.CostedLaw.expectation_ofReal_fintype _ _ (fun i => hs i 0)]
        simp only [partialObsPMF_toReal, w, dif_neg hc]
        rw [← Finset.sum_mul]
        have hn : (∑ o : Option I, (checkedOutcomePMF hN A j.val o).toReal) = 1 := by
          simp only [checkedOutcomePMF_toReal, Fintype.sum_option]
          linarith [(search_checked_attempt hN A j.val).2.2.2.1]
        rw [hn, one_mul]
    calc
      _ = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (iterationPMF (sizes stage) (hsizes stage))
          (fun j => ENNReal.ofReal (∑ o : Option I,
            (checkedOutcomePMF hN A j.val o).toReal * w j o)) := by
        congr 1
        funext j
        exact heach j
      _ = _ := by
        rw [Qatlib.Concepts.AmplitudeSearch.InterruptMin.CostedLaw.expectation_ofReal_fintype _ _ (fun j =>
          Finset.sum_nonneg fun o _ => mul_nonneg ENNReal.toReal_nonneg (hw j o))]
        congr 1
        rw [interruptedBudgetEval, Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro o _
        rw [← mul_assoc, search_attempt_factor]
        rfl

theorem interrupted_dominates_atomic (hN : 0 < Fintype.card I) (A : Finset I)
    (sizes : ℕ → ℕ) (hsizes : ∀ k, 0 < sizes k) (stage budget : ℕ)
    (f g : I → ℕ → ℝ) (t : ℕ → ℝ)
    (hfg : ∀ i r, r < budget → f i r ≤ g i r)
    (ht : ∀ i r, r ≤ budget → t r ≤ g i 0) :
    FiniteBudgetEval A sizes stage budget f t ≤ interruptedBudgetEval A sizes stage budget g := by
  induction budget using Nat.strong_induction_on generalizing stage with
  | h budget ih =>
    conv_lhs => rw [FiniteBudgetEval]
    conv_rhs => rw [interruptedBudgetEval]
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left _
      ((search_joint_attempt_law hN A (sizes stage) (hsizes stage)).1 x)
    by_cases hc : x.1.val + 1 ≤ budget
    · simp only [dif_pos hc]
      have hb := search_budget_progress _ _ hc
      cases x.2 with
      | some i => exact hfg i _ hb
      | none =>
        exact ih _ hb (stage + 1)
          (fun i r hr => hfg i r (hr.trans hb))
          (fun i r hr => ht i r (hr.trans hb.le))
    · simp only [dif_neg hc]
      have hm : (∑ i : I, partialObsMass A x.1.val budget i) = 1 := by
        simpa only [tsum_fintype] using (partialObsMass_sum_one hN A x.1.val budget).tsum_eq
      calc
        t budget = ∑ i : I, partialObsMass A x.1.val budget i * t budget := by
          rw [← Finset.sum_mul, hm, one_mul]
        _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (ht i budget le_rfl) (partialObsMass_nonneg _ _ _ _)

end Qatlib.Concepts.AmplitudeSearch.InterruptMin
