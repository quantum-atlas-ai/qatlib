/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.CausalSearch.NativeSearch
import Qatlib.Foundations.ProbabilityCore.FiniteBranch.ClockedPaid
import Qatlib.Foundations.ProbabilityCore.FiniteBranch.LawTransport
import Qatlib.Papers.QAOAScaling23.BudgetPrefix.Budget
import Qatlib.Papers.QAOAScaling23.BiasedProcess.CostClasses
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace Qatlib.Papers.QAOAScaling23.CausalSearch
open scoped Classical
open Qatlib.Foundations.ProbabilityCore.FiniteBranch
open Qatlib.Foundations.ProbabilityCore.FiniteBranch.ClockedCode
open BiasedProcess
variable {I : Type}

def minimumCode (oracle : I → Code I (Option I)) : ℕ → I → Code I I
  | 0,current => .ret current
  | fuel+1,current => bindCode (oracle current) (fun out => match out with
      | none => .ret current
      | some candidate => .save candidate (fun saved => minimumCode oracle fuel saved))

def rowPayload (rows : (r : ℕ) → Row r)
    (candidate : (r : ℕ) → Fin (rows r).outcomes → I) (r : ℕ)
    (a : Fin (rows r).outcomes) : Option I×ℕ :=
  (if (rows r).bad a then none else some (candidate r a),(rows r).charge a)

theorem minimum_step_law (cost : I → ℝ) (oracle : I → Code I (Option I))
    (hno : ∀ i,NoSave (oracle i)) (rows : (r : ℕ) → Row r)
    (candidate : (r : ℕ) → Fin (rows r).outcomes → I)
    (current : I) (r fuel B : ℕ)
    (hjoint : (paidTree cost current (oracle current)).law=
      ((rows r).law.map (rowPayload rows candidate r))) :
    (run cost current B (minimumCode oracle (fuel+1) current)).law=
      ((.sample (rows r).outcomes (rows r).law (fun a =>
        if (rows r).charge a≤B then
          if (rows r).bad a then .pure (⟨some current,(rows r).charge a,current⟩ : Result I I)
          else (run cost (selectLower cost current (candidate r a)) (B-(rows r).charge a)
            (minimumCode oracle fuel (selectLower cost current (candidate r a)))).map
              (charge ((rows r).charge a))
        else .pure ⟨none,B,current⟩) : Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree (Result I I))).law := by
  rw [minimumCode,run_bind_paid_law cost current B _ (hno current),hjoint,PMF.bind_map]
  rw [Tree.law]
  apply congrArg (PMF.bind (rows r).law)
  funext a
  simp only [Function.comp_def,rowPayload,continuePaid]
  by_cases hc : (rows r).charge a≤B
  · simp only [hc,if_true]
    cases hb : (rows r).bad a with
    | false => simp only [Bool.false_eq_true,if_false,run,Tree.law_map]
    | true => simp only [if_true,run,Tree.law,PMF.pure_map,charge]; rfl
  · simp only [hc,if_false,Tree.law]

def prehitRisk (rows : (r : ℕ) → Row r) (B r : ℕ) : ℝ :=
  (descend rows r).probability (fun tr => tr.oracleBad=true ∨ B<paid tr)

def physicalFailure (rank : I → ℕ) (r : Result I I) : ℝ := if rank r.best=0 then 0 else 1

theorem minimum_preserves_minimum (cost : I → ℝ) (rank : I → ℕ)
    (hzero : ∀ i,rank i=0 ↔ ∀ j,cost i≤cost j)
    (oracle : I → Code I (Option I)) (fuel B : ℕ) (current : I)
    (hmin : rank current=0) :
    (run cost current B (minimumCode oracle fuel current)).All
      (fun out => physicalFailure rank out=0) := by
  apply Tree.all_mono _ (run_preserves_minimum cost _ current ((hzero current).mp hmin) B)
  intro out hout
  simp [physicalFailure,hout,hmin]

theorem prehitRisk_step (rows : (r : ℕ) → Row r) (B r : ℕ) :
    prehitRisk rows B (r+1)=∑ a,((rows r).law a).toReal *
      (if (rows r).bad a then 1 else if B<(rows r).charge a then 1
       else prehitRisk rows (B-(rows r).charge a) ((rows r).next a).val) := by
  rw [prehitRisk,descend,Tree.probability,Tree.mean]
  apply Finset.sum_congr rfl
  intro a _
  rw [Tree.mean_map]
  congr 1
  cases hb : (rows r).bad a with
  | true =>
    simp only [if_true]
    calc
      _=(descend rows ((rows r).next a).val).mean (fun _ => 1) := by
        apply Tree.mean_congr
        apply Tree.all_of_forall
        intro tr
        simp [prepend]
      _=1 := Tree.mean_const _ _
  | false =>
    simp only [Bool.false_eq_true,if_false]
    by_cases hc : B<(rows r).charge a
    · simp only [hc,if_true]
      calc
        _=(descend rows ((rows r).next a).val).mean (fun _ => 1) := by
          apply Tree.mean_congr
          apply Tree.all_of_forall
          intro tr
          have hp : B<paid (prepend (r+1) ((rows r).charge a) false a.val tr) := by
            change B<(rows r).charge a+paid tr
            omega
          simp only [hp,or_true,if_true]
        _=1 := Tree.mean_const _ _
    · simp only [hc,if_false,prehitRisk,Tree.probability]
      apply Tree.mean_congr
      apply Tree.all_of_forall
      intro tr
      congr 1
      apply propext
      simp only [prepend,paid,List.sum_cons,Bool.false_or]
      exact or_congr Iff.rfl (Nat.sub_lt_iff_lt_add' (Nat.le_of_not_gt hc)).symm

theorem physical_failure_le_prehitRisk (cost : I → ℝ) (rank : I → ℕ)
    (hzero : ∀ i,rank i=0 ↔ ∀ j,cost i≤cost j)
    (horder : ∀ i j,rank i<rank j ↔ cost i<cost j)
    (oracle : I → Code I (Option I)) (hno : ∀ i,NoSave (oracle i))
    (rows : (r : ℕ) → Row r)
    (candidate : (r : ℕ) → Fin (rows r).outcomes → I)
    (hnext : ∀ r a,rank (candidate r a)=((rows r).next a).val)
    (hjoint : ∀ current r,rank current=r+1 →
      (paidTree cost current (oracle current)).law=
        ((rows r).law.map (rowPayload rows candidate r)))
    (current : I) (fuel B : ℕ) (hfuel : rank current≤fuel) :
    (run cost current B (minimumCode oracle fuel current)).mean (physicalFailure rank)≤
      prehitRisk rows B (rank current) := by
  generalize hr : rank current=r at hfuel ⊢
  induction r using Nat.strong_induction_on generalizing current fuel B with
  | h r ih =>
    cases r with
    | zero =>
      have he :=
          Tree.mean_congr _ (minimum_preserves_minimum cost rank hzero oracle fuel B current hr)
      rw [he,Tree.mean_const]
      simp [prehitRisk,descend,Tree.probability,Tree.mean,paid]
    | succ r =>
      cases fuel with
      | zero => omega
      | succ fuel =>
        have he :=
            minimum_step_law cost oracle hno rows candidate current r fuel B (hjoint current r hr)
        rw [Tree.mean_eq_of_law_eq _ _ he (physicalFailure rank) (fun out => by
          unfold physicalFailure
          split_ifs <;> norm_num),Tree.mean,prehitRisk_step]
        apply Finset.sum_le_sum
        intro a _
        apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        have hnextlt : rank (candidate r a)<rank current := by
          rw [hnext,hr]
          exact ((rows r).next a).isLt
        have hsel : selectLower cost current (candidate r a)=candidate r a :=
          if_pos ((horder _ _).mp hnextlt)
        by_cases hc : (rows r).charge a≤B
        · simp only [hc,if_true,show ¬B<(rows r).charge a by omega,if_false]
          cases hb : (rows r).bad a with
          | true =>
            simp only [if_true,Tree.mean,physicalFailure]
            simp [hr]
          | false =>
            simp only [Bool.false_eq_true,if_false,hsel,Tree.mean_map]
            change (run cost (candidate r a) (B-(rows r).charge a)
              (minimumCode oracle fuel (candidate r a))).mean (physicalFailure rank)≤_
            rw [← hnext]
            exact ih (rank (candidate r a)) (by omega) (candidate r a) fuel
              (B-(rows r).charge a) rfl (by omega)
        · simp only [hc,if_false,Tree.mean,physicalFailure]
          have hcb : B<(rows r).charge a := by omega
          cases hb : (rows r).bad a <;> simp [hcb,hr]

theorem native_search_paid_law [Fintype I] [DecidableEq I] (cost : I → ℝ) (current : I)
    (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) (seed : I) (S : Finset I)
    (valid : I → Bool) (ms : List ℕ) :
    (paidTree cost current (searchCode U hU seed S valid ms)).law=
      (Qatlib.Concepts.WalkSearch.QuantumAccess.searchForSchedule
        U hU seed S valid ms).map (fun tr => (tr,searchFee tr)) := by
  rw [paidTree_deterministic_fee cost current _ _ (searchCode_returns cost current U hU seed S valid ms),
    searchCode_actual_law]

end Qatlib.Papers.QAOAScaling23.CausalSearch
