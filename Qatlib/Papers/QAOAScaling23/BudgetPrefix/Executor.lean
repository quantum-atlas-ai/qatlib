/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.BudgetPrefix.BadUnion
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QAOAScaling23.BudgetPrefix
open scoped Classical
open Qatlib.Foundations.ProbabilityCore.FiniteBranch
open Qatlib.Papers.QAOAScaling23.BiasedProcess

structure Receipt where
  next : ℕ
  charge : ℕ
  bad : Bool
  sample : ℕ

def receipts : List ℕ → List ℕ → List Bool → List ℕ → List Receipt
  | j::js,c::cs,b::bs,a::as => ⟨j,c,b,a⟩::receipts js cs bs as
  | _,_,_,_ => []

def traceReceipts (tr : Trace) : List Receipt :=
  receipts tr.states.tail tr.charges tr.badRows tr.samples

def execute (B current : ℕ) : List Receipt → ℕ
  | [] => current
  | e::es => if e.charge≤B then
      if e.bad then current else execute (B-e.charge) (min current e.next) es
    else current

def spent (B : ℕ) : List Receipt → ℕ
  | [] => 0
  | e::es => if e.charge≤B then
      if e.bad then e.charge else e.charge+spent (B-e.charge) es
    else B

theorem spent_le (B : ℕ) (es : List Receipt) : spent B es≤B := by
  induction es generalizing B with
  | nil => simp [spent]
  | cons e es ih =>
    simp only [spent]
    split_ifs with hc hb
    · exact hc
    · have h:=ih (B-e.charge); omega
    · rfl

theorem execute_preserves_minimum (B : ℕ) (es : List Receipt) : execute B 0 es=0 := by
  induction es generalizing B with
  | nil => rfl
  | cons e es ih => simp [execute,ih]

theorem descend_head (rows : (r : ℕ) → Row r) (r : ℕ) :
    (descend rows r).All (fun tr => tr.states.head?=some r) := by
  cases r with
  | zero => simp [descend,Tree.All]
  | succ r =>
    rw [descend]
    change ∀ a, ((descend rows ((rows r).next a).val).map _).All _
    intro a
    rw [Tree.all_map]
    apply Tree.all_of_forall
    intro tr
    rfl

theorem receipts_prepend (r cost sample j : ℕ) (bad : Bool) (tr : Trace)
    (hhead : tr.states.head?=some j) :
    traceReceipts (prepend r cost bad sample tr)=
      ⟨j,cost,bad,sample⟩::traceReceipts tr := by
  cases hs : tr.states with
  | nil => simp [hs] at hhead
  | cons k ks =>
    have hk : k=j := by simpa [hs] using hhead
    subst k
    simp [traceReceipts,prepend,receipts,hs]

theorem descend_budget_correct (rows : (r : ℕ) → Row r) (r : ℕ) :
    (descend rows r).All (fun tr => ∀ B, paid tr≤B → tr.oracleBad=false →
      execute B r (traceReceipts tr)=0) := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero => simp [descend,Tree.All,traceReceipts,receipts,execute]
    | succ r =>
      rw [descend]
      change ∀ a, ((descend rows ((rows r).next a).val).map _).All _
      intro a
      rw [Tree.all_map]
      have hchild := (Tree.all_and _ _ _).2
        ⟨ih _ ((rows r).next a).isLt,descend_head rows ((rows r).next a).val⟩
      apply Tree.all_mono _ hchild
      intro tr ht B hpaid hbad
      have hb : (rows r).bad a=false ∧ tr.oracleBad=false := by
        simpa only [prepend,Bool.or_eq_false_iff] using hbad
      have hcost : (rows r).charge a≤B := by
        simpa only [paid,prepend,List.sum_cons] using Nat.le_trans (Nat.le_add_right _ _) hpaid
      have hremain : paid tr≤B-(rows r).charge a := by
        change (rows r).charge a+paid tr≤B at hpaid
        omega
      rw [receipts_prepend _ _ _ _ _ _ ht.2,execute,if_pos hcost,hb.1]
      simp only [Bool.false_eq_true,if_false]
      rw [min_eq_right (Nat.le_of_lt ((rows r).next a).isLt)]
      exact ht.1 _ hremain hb.2
end Qatlib.Papers.QAOAScaling23.BudgetPrefix
