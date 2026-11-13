/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BitColumnAccess.ColumnAssemble.BitColumnValueAccessDefs
import Mathlib.Data.List.FinRange

/-!
# Assembling value queries from bit columns

This module proves that querying each bit column once implements the full value-XOR
transformation, with unitary matrices for both the column operations and the assembled value
query. It also proves correctness for injectively encoded symbols. For background on quantum
input-access models, see [GilyenSuLowWiebe2019].

For arbitrary words containing known matrices and value queries, `expand` preserves matrix
semantics, state evolution, and measurement probabilities. Its column-query count is b times the
original value-query count, and its known-matrix count is unchanged.

## Main statements

* `g1`: column unitarity, equality of the assembled and full value matrices, and exactly b
  columns.
* `g2`: basis-state XOR semantics and recovery of injectively encoded symbols from a zero target
  register.
* `g3`: semantic preservation and exact resource counts for expanded words.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.BitColumnAccess.ColumnAssemble
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

/-- Applying the value-XOR update twice restores the address and target register. -/
theorem valueUpdate_involutive {N b : ℕ} (f : Fin N → Reg b) :
    Function.Involutive (valueUpdate f) := by
  intro x
  apply Prod.ext
  · rfl
  · funext k; simp [valueUpdate]

/-- Applying the same bit-column XOR update twice restores the address and target register. -/
theorem columnUpdate_involutive {N b : ℕ} (f : Fin N → Reg b) (j : Fin b) :
    Function.Involutive (columnUpdate f j) := by
  intro x
  apply Prod.ext
  · rfl
  · funext k; by_cases h : k=j <;> simp [columnUpdate, h]

/-- Multiplying the matrices associated with finite functions σ and τ gives the matrix
associated with the composition σ ∘ τ. -/
private theorem perm_comp {I : Type} [Fintype I] [DecidableEq I] (σ τ : I → I) :
    permMatrix σ * permMatrix τ = permMatrix (σ ∘ τ) := by
  ext a b
  simp only [permMatrix, Matrix.mul_apply, Matrix.of_apply, Function.comp_apply]
  rw [Finset.sum_eq_single (τ b)]
  · simp
  · intro k _ hk
    rw [if_neg hk, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The matrix product for a list of column operations equals the matrix of their successive
updates, with the list applied from left to right. -/
theorem column_list {N b : ℕ} (f : Fin N → Reg b) (js : List (Fin b)) :
    (js.map (columnMatrix f)).reverse.prod =
      permMatrix (fun x => js.foldl (fun y j => columnUpdate f j y) x) := by
  induction js with
  | nil => ext a b; simp [permMatrix, Matrix.one_apply]
  | cons j js ih =>
    simp only [List.map_cons, List.reverse_cons, List.prod_append, List.prod_singleton, ih,
      columnMatrix, perm_comp, List.foldl_cons, Function.comp_def]

/-- Applying a list of distinct column updates preserves the address and XORs exactly the target
bits whose indices occur in the list. -/
theorem columns_fold {N b : ℕ} (f : Fin N → Reg b) (js : List (Fin b))
    (hj : js.Nodup) (x : Fin N × Reg b) :
    js.foldl (fun y j => columnUpdate f j y) x =
      (x.1, fun k => if k ∈ js then x.2 k ^^ f x.1 k else x.2 k) := by
  induction js generalizing x with
  | nil => simp
  | cons j js ih =>
    obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hj
    rw [List.foldl_cons, ih htail]
    apply Prod.ext
    · rfl
    · funext k
      by_cases hk : k=j
      · subst k; simp [columnUpdate, hnot]
      · simp [columnUpdate, hk]

/-- Every bit-column matrix is unitary, their ordered product equals the full value-XOR matrix,
the value matrix is unitary, and the complete column list has length b. -/
theorem g1 : ∀ (N b : ℕ) (f : Fin N → Reg b),
    (∀ j, columnMatrix f j ∈ Matrix.unitaryGroup (Fin N × Reg b) ℂ) ∧
    columnWord f = valueMatrix f ∧ valueMatrix f ∈ Matrix.unitaryGroup (Fin N × Reg b) ℂ ∧
    (columns b).length = b := by
  intro N b f
  have hd : (columns b).Nodup := List.nodup_ofFn.mpr Function.injective_id
  have he : (fun x => (columns b).foldl (fun y j => columnUpdate f j y) x) = valueUpdate f := by
    funext x
    rw [columns_fold f (columns b) hd x]
    simp [columns, valueUpdate]
  refine ⟨fun j => permMatrix_unitary (columnUpdate_involutive f j), ?_,
    permMatrix_unitary (valueUpdate_involutive f), ?_⟩
  · unfold columnWord valueMatrix
    rw [column_list, he]
  · simp [columns]

/-- For an injective symbol encoding, the assembled column word XORs the encoded function value
into a basis-state target register. Starting with a zero target register, equality with an
encoded symbol is equivalent to equality of the original symbols. -/
theorem g2 : ∀ (N M b : ℕ) (e : Fin M ↪ Reg b) (f : Fin N → Fin M)
    (x : Fin N) (t : Reg b),
    ApplyGate (columnWord (fun i => e (f i))) (Qatlib.Foundations.PureStateMath.Ket (x,t)) =
      Qatlib.Foundations.PureStateMath.Ket (x, fun j => t j ^^ e (f x) j) ∧
    ∀ y : Fin M, (fun j => false ^^ e (f x) j) = e y ↔ f x = y := by
  intro N M b e f x t
  constructor
  · rw [(g1 N b _).2.1]
    exact applyGate_permMatrix_ket (valueUpdate_involutive _) (x,t)
  · intro y
    simp

/-- Evaluating a concatenated column word multiplies the matrix of the second word by the matrix
of the first word. -/
private theorem evalColumns_append {N b : ℕ} (f : Fin N → Reg b)
    (p q : List (ColumnStep N b)) :
    evalColumns f (p++q) = evalColumns f q * evalColumns f p := by
  simp [evalColumns, List.map_append, List.reverse_append, List.prod_append]

/-- The column-query count is additive under word concatenation. -/
private theorem columnQueries_append {N b : ℕ} (p q : List (ColumnStep N b)) :
    columnQueries (p++q) = columnQueries p + columnQueries q := by
  simp [columnQueries, List.countP_append]

/-- The known-matrix step count is additive under concatenation of column words. -/
private theorem columnGates_append {N b : ℕ} (p q : List (ColumnStep N b)) :
    columnGates (p++q) = columnGates p + columnGates q := by
  have hp : columnQueries p ≤ p.length := List.countP_le_length
  have hq : columnQueries q ≤ q.length := List.countP_le_length
  simp only [columnGates, List.length_append, columnQueries_append]
  omega

/-- The word querying every bit column once contains exactly b column queries. -/
private theorem columnQueries_all (N b : ℕ) :
    columnQueries ((columns b).map (ColumnStep.query : Fin b → ColumnStep N b)) = b := by
  unfold columnQueries
  rw [List.countP_map]
  change (columns b).countP (fun _ => true)=b
  simp [columns]

/-- The word querying every bit column once contains no known-matrix steps. -/
private theorem columnGates_all (N b : ℕ) :
    columnGates ((columns b).map (ColumnStep.query : Fin b → ColumnStep N b)) = 0 := by
  unfold columnGates
  rw [columnQueries_all, List.length_map]
  simp [columns]

/-- Evaluating one query to each bit column gives the full value-XOR matrix. -/
private theorem evalColumns_all {N b : ℕ} (f : Fin N → Reg b) :
    evalColumns f ((columns b).map ColumnStep.query) = valueMatrix f := by
  simpa [evalColumns, columnWord, List.map_map, Function.comp_def] using (g1 N b f).2.1

/-- Replacing each value query by all bit-column queries preserves the evaluated matrix of a
word. -/
private theorem expansion_semantics {N b : ℕ} (f : Fin N → Reg b) (W : List (ValueStep N b)) :
    evalColumns f (expand W) = evalValue f W := by
  induction W with
  | nil => rfl
  | cons s W ih =>
    cases s with
    | known A =>
      rw [show expand (.known A::W)=[.known A]++expand W from rfl,
        evalColumns_append, ih]
      rw [show evalColumns f ([.known A] : List (ColumnStep N b))=A by simp [evalColumns]]
      simp [evalValue]
    | query =>
      rw [expand, List.flatMap_cons, evalColumns_append, evalColumns_all]
      change evalColumns f (expand W) * valueMatrix f = _
      rw [ih]
      simp [evalValue]

/-- Prepending a known matrix to a value word increases its known-matrix step count by one. -/
private theorem valueGates_known {N b : ℕ} (A : Matrix (Fin N × Reg b) (Fin N × Reg b) ℂ)
    (W : List (ValueStep N b)) : valueGates (.known A::W)=1+valueGates W := by
  have hv : valueQueries W ≤ W.length := List.countP_le_length
  simp only [valueGates, valueQueries, List.length_cons, List.countP_cons,
    Bool.false_eq_true, if_false, Nat.add_zero]
  unfold valueQueries at hv
  omega

/-- Prepending a value query leaves the known-matrix step count unchanged. -/
private theorem valueGates_query {N b : ℕ} (W : List (ValueStep N b)) :
    valueGates (.query::W)=valueGates W := by
  simp only [valueGates, valueQueries, List.length_cons, List.countP_cons, ↓reduceIte]
  omega

/-- Expanding a value word multiplies its query count by b and preserves its known-matrix step
count. -/
private theorem expansion_resources {N b : ℕ} (W : List (ValueStep N b)) :
    columnQueries (expand W) = b*valueQueries W ∧ columnGates (expand W) = valueGates W := by
  induction W with
  | nil => simp [expand, columnQueries, columnGates, valueQueries, valueGates]
  | cons s W ih =>
    cases s with
    | known A =>
      rw [show expand (.known A::W)=[.known A]++expand W from rfl,
        columnQueries_append, columnGates_append,
        show columnQueries ([.known A] : List (ColumnStep N b))=0 from rfl,
        show columnGates ([.known A] : List (ColumnStep N b))=1 from rfl, ih.1, ih.2,
        valueGates_known]
      constructor
      · simp [valueQueries]
      · rfl
    | query =>
      rw [show expand (.query::W)=(columns b).map ColumnStep.query++expand W from rfl,
        columnQueries_append, columnGates_append, columnQueries_all, columnGates_all,
        ih.1, ih.2, valueGates_query]
      constructor
      · simp [valueQueries, Nat.mul_add, Nat.add_comm]
      · simp

/-- Expanding value queries into bit-column queries preserves the word matrix, uses b column
queries per original value query, and preserves the known-matrix count. Consequently, it
preserves the resulting state and every finite measurement-event probability for any input
state. -/
theorem g3 : ∀ (N b : ℕ) (f : Fin N → Reg b) (W : List (ValueStep N b)),
    evalColumns f (expand W) = evalValue f W ∧
    columnQueries (expand W) = b*valueQueries W ∧ columnGates (expand W) = valueGates W ∧
    ∀ (ψ : QState (Fin N × Reg b)) (E : Finset (Fin N × Reg b)),
      ApplyGate (evalColumns f (expand W)) ψ = ApplyGate (evalValue f W) ψ ∧
      MeasureProb (ApplyGate (evalColumns f (expand W)) ψ) E =
        MeasureProb (ApplyGate (evalValue f W) ψ) E := by
  intro N b f W
  have hs := expansion_semantics f W
  obtain ⟨hq,hg⟩ := expansion_resources W
  refine ⟨hs,hq,hg,?_⟩
  intro ψ E
  rw [hs]
  exact ⟨rfl,rfl⟩

end
end Qatlib.Concepts.BitColumnAccess.ColumnAssemble
