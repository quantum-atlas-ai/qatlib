/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.IsBotOne
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Ring.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Nat
import Mathlib.Order.RelClasses
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.Positivity.Core

set_option autoImplicit false

namespace Qatlib.Concepts.QueryComplexity.AdaptiveInfo.ClassicalDefs

inductive QueryTree (I A Y : Type) where
  | leaf : Y → QueryTree I A Y
  | ask : I → (A → QueryTree I A Y) → QueryTree I A Y

def run {I A Y : Type} (oracle : I → A) : QueryTree I A Y → Y × ℕ
  | .leaf y => (y,0)
  | .ask q next => let result := run oracle (next (oracle q)); (result.1,result.2+1)

noncomputable def depth {I A Y : Type} [Fintype A] : QueryTree I A Y → ℕ
  | .leaf _ => 0
  | .ask _ next => Finset.univ.sup (fun a => depth (next a)) + 1

noncomputable def outputs {I A Y : Type} [Fintype A] [DecidableEq Y] :
    QueryTree I A Y → Finset Y
  | .leaf y => {y}
  | .ask _ next => Finset.univ.biUnion (fun a => outputs (next a))

theorem run_mem_outputs {I A Y : Type} [Fintype A] [DecidableEq Y]
    (oracle : I → A) (tree : QueryTree I A Y) : (run oracle tree).1 ∈ outputs tree := by
  induction tree with
  | leaf y => simp [run,outputs]
  | ask q next ih =>
    simp only [run,outputs,Finset.mem_biUnion,Finset.mem_univ,true_and]
    exact ⟨oracle q,ih (oracle q)⟩

theorem run_queries_le_depth {I A Y : Type} [Fintype A]
    (oracle : I → A) (tree : QueryTree I A Y) : (run oracle tree).2 ≤ depth tree := by
  induction tree with
  | leaf y => simp [run,depth]
  | ask q next ih =>
    simp only [run,depth]
    exact Nat.add_le_add_right ((ih (oracle q)).trans
      (Finset.le_sup (f:=fun a : A => depth (next a)) (Finset.mem_univ _))) 1

theorem outputs_card_le {I A Y : Type} [Fintype A] [Nonempty A] [DecidableEq Y]
    (tree : QueryTree I A Y) : (outputs tree).card ≤ (Fintype.card A)^(depth tree) := by
  classical
  induction tree with
  | leaf y => simp [outputs,depth]
  | ask q next ih =>
    simp only [outputs,depth]
    calc
      _ ≤ ∑ a, (outputs (next a)).card := Finset.card_biUnion_le
      _ ≤ ∑ a, (Fintype.card A)^(depth (next a)) := Finset.sum_le_sum (fun a _ => ih a)
      _ ≤ ∑ _ : A, (Fintype.card A)^(Finset.univ.sup (fun a => depth (next a))) := by
        apply Finset.sum_le_sum
        intro a _
        exact Nat.pow_le_pow_right (Fintype.card_pos (α:=A))
          (Finset.le_sup (f:=fun a : A => depth (next a)) (Finset.mem_univ a))
      _ = _ := by simp [pow_succ, Nat.mul_comm]

theorem exact_recovery_card {I A Y : Type} [Fintype A] [Nonempty A]
    [Fintype Y] [DecidableEq Y] (oracle : Y → I → A) (tree : QueryTree I A Y)
    (hcorrect : ∀ y, (run (oracle y) tree).1 = y) :
    Fintype.card Y ≤ (Fintype.card A)^(depth tree) := by
  have hsub : Finset.univ ⊆ outputs tree := by
    intro y _
    rw [← hcorrect y]
    exact run_mem_outputs (oracle y) tree
  have hcard : Fintype.card Y ≤ (outputs tree).card := by simpa using Finset.card_le_card hsub
  exact hcard.trans (outputs_card_le tree)

theorem bounded_recovery_card {I A Y : Type} [Fintype A] [Nonempty A] [DecidableEq Y]
    (oracle : Y → I → A) (tree : QueryTree I A Y) :
    ∀ (S : Finset Y) (M : ℕ),
      (∀ y ∈ S, (run (oracle y) tree).1 = y) →
      (∀ y ∈ S, (run (oracle y) tree).2 ≤ M) → S.card ≤ (Fintype.card A)^M := by
  classical
  induction tree with
  | leaf value =>
    intro S M hcorrect _
    have hs : S ⊆ {value} := by
      intro y hy
      have h := hcorrect y hy
      simpa only [run, Finset.mem_singleton] using h.symm
    have hc : S.card ≤ 1 := by simpa using Finset.card_le_card hs
    exact hc.trans (by
      have h : 0<(Fintype.card A)^M := Nat.pow_pos (Fintype.card_pos (α:=A))
      omega)
  | ask q next ih =>
    intro S M hcorrect hcost
    cases M with
    | zero =>
      have hs : S = ∅ := by
        apply Finset.ext
        intro y
        simp
        intro hy
        have hc := hcost y hy
        simp [run] at hc
      simp [hs]
    | succ M =>
      have hbranch (a : A) : (S.filter (fun y => oracle y q=a)).card ≤ (Fintype.card A)^M := by
        apply ih a
        · intro y hy
          obtain ⟨hy,ha⟩ := Finset.mem_filter.mp hy
          simpa only [run,ha] using hcorrect y hy
        · intro y hy
          obtain ⟨hy,ha⟩ := Finset.mem_filter.mp hy
          have h := hcost y hy
          simp only [run,ha] at h
          omega
      calc
        S.card = ∑ a : A, (S.filter (fun y => oracle y q=a)).card := by
          simp only [Finset.card_filter]
          rw [Finset.sum_comm]
          simp
        _ ≤ ∑ _ : A, (Fintype.card A)^M := Finset.sum_le_sum (fun a _ => hbranch a)
        _ = _ := by simp [pow_succ,Nat.mul_comm]

theorem actual_exact_recovery_card {I A Y : Type} [Fintype A] [Nonempty A]
    [Fintype Y] [DecidableEq Y] (oracle : Y → I → A) (tree : QueryTree I A Y) (M : ℕ)
    (hcorrect : ∀ y, (run (oracle y) tree).1 = y)
    (hcost : ∀ y, (run (oracle y) tree).2 ≤ M) : Fintype.card Y ≤ (Fintype.card A)^M := by
  simpa only [Finset.card_univ] using bounded_recovery_card oracle tree Finset.univ M
    (fun y _ => hcorrect y) (fun y _ => hcost y)

theorem actual_kraft {I A Y : Type} [Fintype A] [Nonempty A] [DecidableEq Y]
    (oracle : Y → I → A) (tree : QueryTree I A Y) :
    ∀ S : Finset Y, (∀ y ∈ S, (run (oracle y) tree).1 = y) →
      ∑ y ∈ S, (1/(Fintype.card A:ℝ))^((run (oracle y) tree).2) ≤ 1 := by
  classical
  induction tree with
  | leaf value =>
    intro S hcorrect
    have hs : S ⊆ {value} := by
      intro y hy
      have h := hcorrect y hy
      simpa only [run,Finset.mem_singleton] using h.symm
    have hc : S.card ≤ 1 := by simpa using Finset.card_le_card hs
    simpa only [run,pow_zero,Finset.sum_const,nsmul_eq_mul,mul_one] using
      (show (S.card:ℝ) ≤ 1 from by exact_mod_cast hc)
  | ask q next ih =>
    intro S hcorrect
    have hbranch (a : A) :
        ∑ y ∈ S.filter (fun y => oracle y q=a),
          (1/(Fintype.card A:ℝ))^((run (oracle y) (next a)).2) ≤ 1 := by
      apply ih a
      intro y hy
      obtain ⟨hy,ha⟩ := Finset.mem_filter.mp hy
      simpa only [run,ha] using hcorrect y hy
    calc
      _ = ∑ a : A, ∑ y ∈ S.filter (fun y => oracle y q=a),
          (1/(Fintype.card A:ℝ))^((run (oracle y) (.ask q next)).2) := by
        simp only [Finset.sum_filter]
        rw [Finset.sum_comm]
        simp
      _ = ∑ a : A, (∑ y ∈ S.filter (fun y => oracle y q=a),
          (1/(Fintype.card A:ℝ))^((run (oracle y) (next a)).2)) * (1/(Fintype.card A:ℝ)) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro y hy
        have ha := (Finset.mem_filter.mp hy).2
        simp only [run,ha,pow_succ]
      _ ≤ ∑ _ : A, 1 * (1/(Fintype.card A:ℝ)) :=
        Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_right (hbranch a) (by positivity))
      _ = 1 := by
        simp only [one_mul,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
        have hD : (Fintype.card A:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
        field_simp

end Qatlib.Concepts.QueryComplexity.AdaptiveInfo.ClassicalDefs
