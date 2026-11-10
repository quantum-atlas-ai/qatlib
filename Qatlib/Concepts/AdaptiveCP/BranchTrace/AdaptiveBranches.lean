/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.AdaptiveHistoryDefs
import Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib
open scoped BigOperators

variable {O : Type} [Fintype O] [DecidableEq O] {D : ℕ}

lemma completelyPositive_id :
    CompletelyPositive (LinearMap.id : Operator D →ₗ[ℂ] Operator D) := by
  intro r A hA
  simpa [ChannelAmplification] using! hA

omit [DecidableEq O] in

lemma branch_cp (policy : List O → Instrument O D D) (h : List O) :
    ∀ n, ∀ xs : Fin n → O, CompletelyPositive (branch policy h (List.ofFn xs)) := by
  intro n
  induction n generalizing h with
  | zero =>
    intro xs
    have hempty : List.ofFn xs = ([] : List O) := by simp [List.ofFn_zero]
    simpa [hempty, branch] using completelyPositive_id
  | succ n ih =>
    intro xs
    have hcons : List.ofFn xs = xs 0 :: List.ofFn (Fin.tail xs) := by
      have h := List.ofFn_cons (xs 0) (Fin.tail xs)
      rwa [Fin.cons_self_tail xs] at h
    rw [hcons, branch]
    exact (ih (h ++ [xs 0]) (Fin.tail xs)).comp ((policy h).cp (xs 0))

omit [DecidableEq O] in

lemma branch_trace (policy : List O → Instrument O D D) (h : List O) :
    ∀ n (ρ : Operator D),
      Matrix.trace (∑ xs : Fin n → O, branch policy h (List.ofFn xs) ρ) = Matrix.trace ρ := by
  intro n
  induction n generalizing h with
  | zero =>
    intro ρ
    rw [Fintype.sum_unique]
    change Matrix.trace (branch policy h [] ρ) = Matrix.trace ρ
    simp [branch]
  | succ n ih =>
    intro ρ
    have hsplit : ∑ xs : Fin (n + 1) → O, branch policy h (List.ofFn xs) ρ =
        ∑ o : O, ∑ ys : Fin n → O,
          branch policy (h ++ [o]) (List.ofFn ys) ((policy h).branch o ρ) := by
      have heq := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => O))
        (fun p : O × (Fin n → O) =>
          branch policy (h ++ [p.1]) (List.ofFn p.2) ((policy h).branch p.1 ρ))
        (fun xs => branch policy h (List.ofFn xs) ρ) ?_
      · rw [← heq, Fintype.sum_prod_type]
      · intro p
        dsimp [Fin.consEquiv]
        rw [List.ofFn_cons, branch, LinearMap.comp_apply]

    rw [hsplit, Matrix.trace_sum]
    have hinner : ∀ o : O,
        Matrix.trace (∑ ys : Fin n → O,
          branch policy (h ++ [o]) (List.ofFn ys) ((policy h).branch o ρ)) =
        Matrix.trace ((policy h).branch o ρ) :=
      fun o => ih (h ++ [o]) ((policy h).branch o ρ)
    simp_rw [hinner, ← Matrix.trace_sum]
    exact (policy h).total ρ

theorem g1 :
    ∀ (O : Type) [Fintype O] [DecidableEq O] (D n : ℕ)
      (policy : List O → Instrument O D D) (h : List O),
      (∀ xs : Fin n → O, CompletelyPositive (branch policy h (List.ofFn xs))) ∧
      (∀ ρ : Operator D,
        Matrix.trace (∑ xs : Fin n → O, branch policy h (List.ofFn xs) ρ) = Matrix.trace ρ) := by
  intro O _ _ D n policy h
  exact ⟨branch_cp policy h n, branch_trace policy h n⟩

end Qatlib.Concepts.AdaptiveCP.BranchTrace
