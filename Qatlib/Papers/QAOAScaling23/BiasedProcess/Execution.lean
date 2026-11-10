/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QAOAScaling23.BiasedProcess
open scoped Classical
open Qatlib.Foundations.ProbabilityCore.FiniteBranch

structure Row (r : ℕ) where
  outcomes : ℕ
  law : PMF (Fin outcomes)
  next : Fin outcomes → Fin (r+1)
  charge : Fin outcomes → ℕ
  bad : Fin outcomes → Bool

structure Trace where
  states : List ℕ
  charges : List ℕ
  oracleBad : Bool
  output : ℕ
  badRows : List Bool
  samples : List ℕ

def prepend (r cost : ℕ) (bad : Bool) (sample : ℕ) (tr : Trace) : Trace :=
  ⟨r::tr.states,cost::tr.charges,bad||tr.oracleBad,tr.output,bad::tr.badRows,sample::tr.samples⟩

def descend (rows : (r : ℕ) → Row r) : (r : ℕ) → Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree Trace
  | 0 => .pure ⟨[0],[],false,0,[],[]⟩
  | r+1 => .sample (rows r).outcomes (rows r).law (fun a =>
      (descend rows ((rows r).next a).val).map (prepend (r+1) ((rows r).charge a) ((rows r).bad a) a.val))
termination_by r => r

def initialized {L : ℕ} (p : PMF (Fin L)) (rows : (r : ℕ) → Row r) : Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree Trace :=
  .sample L p (fun i => descend rows i.val)

def paid (tr : Trace) : ℕ := tr.charges.sum

def visits (j : ℕ) (tr : Trace) : ℝ := ((tr.states.count j : ℕ) : ℝ)

theorem descend_minimum (rows : (r : ℕ) → Row r) (r : ℕ) :
    (descend rows r).All (fun tr => tr.output=0) := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero => simp [descend,Tree.All]
    | succ r =>
      rw [descend]
      change ∀ a, ((descend rows ((rows r).next a).val).map _).All _
      intro a
      rw [Tree.all_map]
      exact ih ((rows r).next a).val ((rows r).next a).isLt

theorem descend_states_le (rows : (r : ℕ) → Row r) (r : ℕ) :
    (descend rows r).All (fun tr => ∀ j ∈ tr.states, j≤r) := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero => simp [descend,Tree.All]
    | succ r =>
      rw [descend]
      change ∀ a, ((descend rows ((rows r).next a).val).map _).All _
      intro a
      rw [Tree.all_map]
      apply Tree.all_mono _ (ih _ ((rows r).next a).isLt)
      intro tr htr j hj
      rcases List.mem_cons.1 hj with hj|hj
      · exact hj.le
      · exact (htr j hj).trans (Nat.le_of_lt ((rows r).next a).isLt)
end Qatlib.Papers.QAOAScaling23.BiasedProcess
