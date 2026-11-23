/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AnyCircuit08.MainResults.Basic

/-!
# Adaptive Boolean queries in the dispersing-circuit oracle problem

The classical argument in [HallgrenHarrow2008], Theorem 9, counts the possible reply words
of an adaptive procedure. A finite query tree evaluates against the same Boolean response
function as the phase query. Randomized procedures are finite probability mixtures of trees.
-/

@[expose] public section

open scoped BigOperators

namespace Qatlib.Papers.AnyCircuit08.MainResults

open Qatlib.Papers.AnyCircuit08.MainResults

/-- A depth-indexed deterministic decision tree for a Boolean oracle. A procedure with an
upper query budget can pad shorter branches with dummy queries on a nonempty query register. -/
inductive BitQueryTree (X A : Type) : ℕ → Type
  | guess (answer : Option A) : BitQueryTree X A 0
  | ask {q : ℕ} (query : X) (next : Bool → BitQueryTree X A q) : BitQueryTree X A (q + 1)

/-- Evaluate the queries against one oracle and retain their replies in chronological order. -/
def BitQueryTree.replies {X A : Type} {q : ℕ}
    (tree : BitQueryTree X A q) (oracle : X → Bool) : Fin q → Bool :=
  match tree with
  | .guess _ => Fin.elim0
  | .ask x next => Fin.cases (oracle x) ((next (oracle x)).replies oracle)

/-- Decode a reply word by following the corresponding branches of the tree. -/
def BitQueryTree.decode {X A : Type} {q : ℕ}
    (tree : BitQueryTree X A q) (word : Fin q → Bool) : Option A :=
  match tree with
  | .guess answer => answer
  | .ask _ next => (next (word 0)).decode (word ∘ Fin.succ)

/-- Execute a deterministic procedure against an oracle supplied for one secret. -/
def BitQueryTree.run {X A : Type} {q : ℕ}
    (tree : BitQueryTree X A q) (oracle : X → Bool) : Option A :=
  match tree with
  | .guess answer => answer
  | .ask x next => (next (oracle x)).run oracle

/-- Decoding the actual reply word agrees with executing the adaptive procedure. -/
theorem BitQueryTree.decode_replies {X A : Type} {q : ℕ}
    (tree : BitQueryTree X A q) (oracle : X → Bool) :
    tree.decode (tree.replies oracle) = tree.run oracle := by
  induction tree with
  | guess => rfl
  | ask x next ih =>
    simpa only [replies, decode, run, Fin.cases_zero, Function.comp_def, Fin.cases_succ] using
      ih (oracle x)

/-- The uniform success probability of the adaptive tree for the response family `f`. -/
noncomputable def BitQueryTree.successProbability {X A : Type} [Fintype A] {q : ℕ}
    (tree : BitQueryTree X A q) (f : A → X → Bool) : ℝ := by
  classical
  exact ((Finset.univ.filter fun a => tree.run (f a) = some a).card : ℝ) / Fintype.card A

/-- The classical transcript estimate of [HallgrenHarrow2008], Theorem 9, applied to the
actual replies of an adaptive Boolean query procedure. -/
theorem BitQueryTree.successProbability_le {X A : Type} [Fintype A] {n q : ℕ} {α : ℝ}
    (hA : (2 : ℝ) ^ (α * (n : ℝ)) ≤ Fintype.card A)
    (tree : BitQueryTree X A q) (f : A → X → Bool) :
    tree.successProbability f ≤ (2 : ℝ) ^ ((q : ℝ) - α * (n : ℝ)) := by
  classical
  let alg : ClassicalQueryAlgorithm A q := ⟨fun a => tree.replies (f a), tree.decode⟩
  simpa [BitQueryTree.successProbability, ClassicalQueryAlgorithm.successSet, alg,
    tree.decode_replies] using theorem9_classical_average hA alg

/-- A randomized mixture of adaptive trees achieving average success at least `δ > 0`
needs at least `α * n + log₂ δ` Boolean queries [HallgrenHarrow2008], Theorem 9. -/
theorem BitQueryTree.randomized_queries_ge {X A R : Type} [Fintype A] [Fintype R]
    {n q : ℕ} {α δ : ℝ} (hA : (2 : ℝ) ^ (α * (n : ℝ)) ≤ Fintype.card A)
    (hδ : 0 < δ) (trees : R → BitQueryTree X A q) (f : A → X → Bool)
    (weight : R → ℝ) (hw : ∀ r, 0 ≤ weight r) (hsum : ∑ r, weight r = 1)
    (hsucc : δ ≤ ∑ r, weight r * (trees r).successProbability f) :
    α * (n : ℝ) + Real.logb 2 δ ≤ (q : ℝ) := by
  have hbound : (∑ r, weight r * (trees r).successProbability f) ≤
      (2 : ℝ) ^ ((q : ℝ) - α * (n : ℝ)) := calc
    _ ≤ ∑ r, weight r * (2 : ℝ) ^ ((q : ℝ) - α * (n : ℝ)) :=
      Finset.sum_le_sum fun r _ =>
        mul_le_mul_of_nonneg_left ((trees r).successProbability_le hA f) (hw r)
    _ = _ := by rw [← Finset.sum_mul, hsum, one_mul]
  have hlog := Real.logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num) hδ (hsucc.trans hbound)
  rw [Real.logb_rpow (by norm_num) (by norm_num)] at hlog
  linarith

end Qatlib.Papers.AnyCircuit08.MainResults
