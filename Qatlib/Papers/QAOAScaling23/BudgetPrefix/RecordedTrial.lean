/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.BudgetPrefix.Executor
import Qatlib.Papers.QAOAScaling23.FreshRepeat.ActualLaw
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QAOAScaling23.BudgetPrefix
open scoped Classical
open Qatlib.Foundations.ProbabilityCore.FiniteBranch
open Qatlib.Papers.QAOAScaling23.BiasedProcess

def observedCharges (B : ℕ) : List Receipt → List ℕ
  | [] => []
  | e::es => if e.charge≤B then
      if e.bad then [e.charge] else e.charge::observedCharges (B-e.charge) es
    else [B]

def observedStates (B current : ℕ) : List Receipt → List ℕ
  | [] => [current]
  | e::es => if e.charge≤B then
      if e.bad then [current] else current::observedStates (B-e.charge) (min current e.next) es
    else [current]

def observedSamples (B : ℕ) : List Receipt → List ℕ
  | [] => []
  | e::es => if e.charge≤B then
      if e.bad then [e.sample] else e.sample::observedSamples (B-e.charge) es
    else []

def observedBadRows (B : ℕ) : List Receipt → List Bool
  | [] => []
  | e::es => if e.charge≤B then
      if e.bad then [true] else false::observedBadRows (B-e.charge) es
    else []

theorem observedCharges_sum (B : ℕ) (es : List Receipt) :
    (observedCharges B es).sum=spent B es := by
  induction es generalizing B with
  | nil => rfl
  | cons e es ih =>
    simp only [observedCharges,spent]
    split_ifs <;> simp_all

def budgetSummary (B initialFee : ℕ) (tr : Trace) : Trace :=
  let es := traceReceipts tr
  let rem := B-initialFee
  let start := tr.states.headD tr.output
  ⟨observedStates rem start es,initialFee::observedCharges rem es,
    (observedBadRows rem es).contains true,execute rem start es,
    observedBadRows rem es,observedSamples rem es⟩

theorem budgetSummary_paid (B initialFee : ℕ) (tr : Trace) :
    paid (budgetSummary B initialFee tr)=initialFee+spent (B-initialFee) (traceReceipts tr) := by
  simp [paid,budgetSummary,observedCharges_sum]

theorem budgetSummary_paid_le (B initialFee : ℕ) (hinit : initialFee≤B) (tr : Trace) :
    paid (budgetSummary B initialFee tr)≤B := by
  rw [budgetSummary_paid]
  have h:=spent_le (B-initialFee) (traceReceipts tr)
  omega

theorem headD_of_head {tr : Trace} {r : ℕ} (h : tr.states.head?=some r) :
    tr.states.headD tr.output=r := by
  cases hs : tr.states with
  | nil => simp [hs] at h
  | cons k ks => simpa [hs] using h

theorem initialized_budget_output {L : ℕ} (p : PMF (Fin L)) (rows : (r : ℕ) → Row r)
    (B initialFee : ℕ) :
    (initialized p rows).All (fun tr => tr.oracleBad=false → initialFee+paid tr≤B →
      (budgetSummary B initialFee tr).output=0) := by
  change ∀ i : Fin L, (descend rows i.val).All _
  intro i
  have h := (Tree.all_and _ _ _).2 ⟨descend_budget_correct rows i.val,descend_head rows i.val⟩
  apply Tree.all_mono _ h
  intro tr ht hbad hpaid
  change execute (B-initialFee) (tr.states.headD tr.output) (traceReceipts tr)=0
  rw [headD_of_head ht.2]
  exact ht.1 _ (by omega) hbad

def budgetTrial {L : ℕ} (p : PMF (Fin L)) (rows : (r : ℕ) → Row r)
    (B initialFee : ℕ) : Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree Trace :=
  (initialized p rows).map (budgetSummary B initialFee)

theorem budgetTrial_path_cap {L : ℕ} (p : PMF (Fin L)) (rows : (r : ℕ) → Row r)
    (B initialFee : ℕ) (hinit : initialFee≤B) :
    (budgetTrial p rows B initialFee).All (fun tr => paid tr≤B) := by
  rw [budgetTrial,Tree.all_map]
  exact Tree.all_of_forall _ (budgetSummary_paid_le B initialFee hinit)
end Qatlib.Papers.QAOAScaling23.BudgetPrefix
