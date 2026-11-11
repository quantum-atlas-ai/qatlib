/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.BudgetPrefix.RecordedTrial

/-!
# Failure and overflow bounds for budgeted descent

This module bounds budgeted trial failure by oracle failure and full-trace cost overflow.
Markov's inequality and the weighted row-charge estimates yield `source_budget_half_failure`,
combining a failure probability at most one half with a pathwise paid-budget bound for the
resource analysis of [ShaydulinEtAl2024].

## Main statements

* `budget_failure_union`: The mean failure indicator of the budgeted trial is at most the sum of
  the full descent's oracle-bad and cost-overflow indicator means.
* `actual_overflow_bound`: For a positive budget, the full descent's overflow probability
  expressed as an indicator mean is at most its mean full cost divided by the budget.
* `source_budget_half_failure`: Under the stated weighted row-charge, oracle-failure,
  initialization, and budget hypotheses, the budgeted trial outputs a nonzero rank with
  probability at most one half and every trace pays at most `B`.

## References

* [Shaydulin et al., 2024][ShaydulinEtAl2024]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QAOAScaling23.BudgetPrefix
open scoped Classical ENNReal
open Qatlib.Foundations.ProbabilityCore.FiniteBranch
open Qatlib.Papers.QAOAScaling23.BiasedProcess
open Qatlib.Papers.QAOAScaling23.WeightedCost
open Qatlib.Papers.QAOAScaling23.FreshRepeat

/-- The initial fee plus the trace's total paid charge, viewed as a real number. -/
def fullCost (initialFee : ℕ) (tr : Trace) : ℝ := ((initialFee+paid tr : ℕ) : ℝ)

/-- The real indicator that the full cost, including the initial fee, strictly exceeds budget
`B`. -/
def overflowIndicator (B initialFee : ℕ) (tr : Trace) : ℝ :=
  if (B:ℝ)<fullCost initialFee tr then 1 else 0

/-- The mean failure indicator of the budgeted trial is at most the sum of the full descent's
oracle-bad and cost-overflow indicator means. -/
theorem budget_failure_union {L : ℕ} (p : PMF (Fin L)) (rows : (r : ℕ) → Row r)
    (B initialFee : ℕ) :
    (budgetTrial p rows B initialFee).mean trialFailure ≤
      (initialized p rows).mean badIndicator +
      (initialized p rows).mean (overflowIndicator B initialFee) := by
  rw [budgetTrial,Tree.mean_map,← Tree.mean_add]
  apply Tree.mean_mono
  apply Tree.all_mono _ (initialized_budget_output p rows B initialFee)
  intro tr hcorrect
  have hf : trialFailure (budgetSummary B initialFee tr)≤1 := by
    unfold trialFailure
    split_ifs <;> norm_num
  have hover : 0≤overflowIndicator B initialFee tr := by
    unfold overflowIndicator
    split_ifs <;> norm_num
  cases hb : tr.oracleBad with
  | true => simpa [badIndicator,hb] using hf.trans (by linarith : (1:ℝ)≤1+overflowIndicator B initialFee tr)
  | false =>
    by_cases ho : (B:ℝ)<fullCost initialFee tr
    · simpa [badIndicator,hb,overflowIndicator,ho] using hf
    · have hpaid : initialFee+paid tr≤B := by
        have h:=le_of_not_gt ho
        change ((initialFee+paid tr:ℕ):ℝ)≤(B:ℝ) at h
        exact_mod_cast h
      have hout:=hcorrect hb hpaid
      simp [trialFailure,hout,badIndicator,hb,overflowIndicator,ho]

/-- For a positive budget, the full descent's overflow probability expressed as an indicator
mean is at most its mean full cost divided by the budget. -/
theorem actual_overflow_bound {L : ℕ} (p : PMF (Fin L)) (rows : (r : ℕ) → Row r)
    (B initialFee : ℕ) (hB : 0<B) :
    (initialized p rows).mean (overflowIndicator B initialFee)≤
      (initialized p rows).mean (fullCost initialFee)/(B:ℝ) := by
  have h := Tree.probability_overflow_le (initialized p rows) (fullCost initialFee)
    (fun _ => Nat.cast_nonneg _) (B:ℝ) (by exact_mod_cast hB)
  have he : (initialized p rows).mean (overflowIndicator B initialFee)=
      (initialized p rows).probability (fun tr => (B:ℝ)<fullCost initialFee tr) := by
    apply Tree.mean_congr
    apply Tree.all_of_forall
    intro tr
    by_cases ho : (B:ℝ)<fullCost initialFee tr <;> simp [overflowIndicator,ho]
  rw [he]
  exact h

/-- Under the stated weighted row-charge, oracle-failure, initialization, and budget hypotheses,
the budgeted trial outputs a nonzero rank with probability at most one half and every trace
pays at most `B`. -/
theorem source_budget_half_failure {L : ℕ} (hL : 0<L) (p : PMF (Fin L)) (q : ℕ → ℝ)
    (hq : ∀ i : Fin L,(p i).toReal=q i.val) (h0 : 0<q 0) (hnn : ∀ j,0≤q j)
    (rows : (r : ℕ) → Row r) (hlaw : RowLaw q rows)
    (C N M ε : ℝ) (hC : 0<C) (hN : 0<N)
    (hM : 1/Real.sqrt (popt q)≤M)
    (hrow : ∀ j,0<j → rowCharge rows j≤2*C*N/Real.sqrt (prefixSum q j))
    (hε : 0≤ε) (hrowBad : ∀ r,rowBadMean rows r≤ε) (hunion : (L:ℝ)*ε≤1/6)
    (B initialFee : ℕ) (hinitFee : (initialFee:ℝ)≤C*N) (hbudget : 15*C*M*N≤(B:ℝ)) :
    (budgetTrial p rows B initialFee).probability (fun tr => tr.output≠0)≤1/2 ∧
      (budgetTrial p rows B initialFee).All (fun tr => paid tr≤B) := by
  have hq01 : q 0≤1 := by
    have h := ENNReal.toReal_mono (by simp : (1:ℝ≥0∞)≠⊤) (PMF.coe_le_one p ⟨0,hL⟩)
    simpa only [hq,Fin.val_zero,ENNReal.toReal_one] using h
  have hsq : 0 < Real.sqrt (popt q) := Real.sqrt_pos.2 h0
  have hsq1 : Real.sqrt (popt q)≤1 := by
    simpa only [popt,Real.sqrt_one] using Real.sqrt_le_sqrt hq01
  have hM1 : 1≤M := ((one_le_div hsq).2 hsq1).trans hM
  have hCN : 0<C*N := mul_pos hC hN
  have hCNM : C*N≤C*M*N := by nlinarith [mul_le_mul_of_nonneg_left hM1 hCN.le]
  have hI : initialFee≤B := by
    have h : (initialFee:ℝ)≤(B:ℝ) := by nlinarith [hbudget,hinitFee,hCNM]
    exact_mod_cast h
  have hBr : 0<(B:ℝ) := by
    have hpos : 0<15*C*M*N := by positivity
    exact hpos.trans_le hbudget
  have hcost := actual_paid_bound hL p q hq h0 hnn rows hlaw C N hC hN.le hrow
  have htotal : (initialized p rows).mean (fullCost initialFee)≤5*C*M*N := by
    have he : (initialized p rows).mean (fullCost initialFee)=
        (initialFee:ℝ)+(initialized p rows).mean (fun tr => (paid tr:ℝ)) := by
      unfold fullCost
      simp only [Nat.cast_add,Tree.mean_add,Tree.mean_const]
    rw [he]
    have hs : 4*C*N/Real.sqrt (popt q)≤4*C*M*N := by
      have h:=mul_le_mul_of_nonneg_left hM (show 0≤4*C*N by positivity)
      convert! h using 1 <;> ring
    linarith
  have hover := actual_overflow_bound p rows B initialFee (by exact_mod_cast hBr)
  have hoverthird : (initialized p rows).mean (overflowIndicator B initialFee)≤1/3 := by
    apply hover.trans
    rw [div_le_iff₀ hBr]
    nlinarith [htotal,hbudget]
  have hbad := (initialized_bad_bound p rows ε hε hrowBad).trans hunion
  have hu := budget_failure_union p rows B initialFee
  rw [trial_failure_probability]
  exact ⟨by linarith [hu,hbad,hoverthird],budgetTrial_path_cap p rows B initialFee hI⟩
end Qatlib.Papers.QAOAScaling23.BudgetPrefix
