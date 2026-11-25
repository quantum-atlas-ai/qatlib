/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CircuitLang.QueryWords
public import Qatlib.Papers.Instantaneous08.MainResults.GraphProgram
public import Qatlib.Papers.Instantaneous08.MainResults.ZNetworkGate

@[expose] public section

/-!
# The Z-network gate word for an X-program

Section 5.3 of [ShepherdBremner2009] compiles the constant-action X-program of `k` rows into a
Z-network: for every row the data coordinates in its support are propagated to one ancilla by
CNOTs, the ancilla is rotated, and the propagations are undone. This module records that gate word
as an explicit `Qatlib.Foundations.QueryWordCore.Circuit.Circuit` over the data-ancilla index set
of `Qatlib.Papers.Instantaneous08.MainResults.DataBus`. Its `Circuit.Size` is
`2 * edgeCount p + k`: two CNOTs per nonzero entry of `p` plus one rotation per row, so the word
has size polynomial in the number of data coordinates `n` and rows `k`. The word's matrix
denotation is the product of the row operators of
`Qatlib.Papers.Instantaneous08.MainResults.rowOperator`, and on the ancilla-zero sector it
multiplies by the same product of character multipliers that appears in
`Qatlib.Papers.Instantaneous08.MainResults.ConstantAction.circuitOp_char`.

The paper counts depth in layers of commuting gates, while `Circuit.Size` counts instructions; the
size bound formalized here is therefore a resource proxy for the depth statement of §5.3, and the
parallel scheduling of the CNOTs is not modeled.

## Main statements

* `rowWord_size`, `zNetworkWord_size`: the exact instruction counts of one row and of the whole
  word.
* `zNetworkWord_size_le`: the word has at most `2 * (n * k) + k` instructions.
* `rowWord_denote`, `zNetworkWord_denote`: the word denotes the product of row operators, which is
  diagonal in the data-ancilla basis.
* `zNetworkWord_mulVec_zero`: on the ancilla-zero sector the word multiplies by
  `∏ i, zCoeff (θ i) (dot (p i) x = 0)`.

## References

* [Shepherd and Bremner, 2009][ShepherdBremner2009], Lemmas 7 and 8 and Section 5.3,
  [arXiv:0809.0847](https://arxiv.org/abs/0809.0847)
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

open Matrix

namespace Qatlib.Papers.Instantaneous08.MainResults

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CircuitLang.QueryWords
open Qatlib.Papers.Instantaneous08.MainResults.XProgram
open Qatlib.Papers.Instantaneous08.MainResults.ConstantAction
open Qatlib.Papers.Instantaneous08.MainResults.GraphProgram

attribute [local instance] Classical.propDecidable

/-- One row of the Z-network: propagate the support of the row to the ancilla, rotate the
ancilla, and propagate back. -/
def rowWord {n : ℕ} (p : F2Vec n) (θ : ℝ) : Circuit (DataBus n) :=
  ((rowEdges p).map cnotInto).map Step.gate ++
    ([Step.gate (ancillaZ θ)] ++ ((rowEdges p).map cnotInto).map Step.gate)

/-- The Z-network gate word of an X-program with `k` rows: the rows are processed in reverse
order, so that the first row's gates are executed last. -/
def zNetworkWord (n : ℕ) : (k : ℕ) → (Fin k → F2Vec n) → (Fin k → ℝ) → Circuit (DataBus n)
  | 0, _, _ => []
  | k + 1, p, θ =>
      zNetworkWord n k (fun i => p i.succ) (fun i => θ i.succ) ++ rowWord (p 0) (θ 0)

/-- The length of the support list of a row is the number of its nonzero entries. -/
theorem rowEdges_length {n : ℕ} (p : F2Vec n) :
    (rowEdges p).length = (Finset.univ.filter (fun j => p j = 1)).card := by
  simp [rowEdges, Finset.length_toList]

/-- Splitting the edge count of `k + 1` rows into the first row and the remaining rows. -/
theorem edgeCount_succ {n k : ℕ} (p : Fin (k + 1) → F2Vec n) :
    edgeCount p = (Finset.univ.filter (fun j => p 0 j = 1)).card +
      ∑ i : Fin k, (Finset.univ.filter (fun j => p i.succ j = 1)).card := by
  rw [edgeCount, Fin.sum_univ_succ]

/-- The gate count of a list of explicit gates is its length. -/
theorem gateCount_gateList {I : Type*} (l : List (Matrix I I ℂ)) :
    GateCount (l.map Step.gate) = l.length := by
  induction l with
  | nil => simp
  | cons g l ih =>
      rw [List.map_cons, gateCount_gate, ih]
      simp

/-- One row of the word has two CNOTs per support coordinate and one rotation. -/
theorem rowWord_size {n : ℕ} (p : F2Vec n) (θ : ℝ) :
    Size (rowWord p θ) = 2 * (rowEdges p).length + 1 := by
  simp [rowWord, Size]
  omega

/-- One row of the word contains exactly as many instructions as gates. -/
theorem rowWord_gateCount {n : ℕ} (p : F2Vec n) (θ : ℝ) :
    GateCount (rowWord p θ) = 2 * (rowEdges p).length + 1 := by
  rw [rowWord, gateCount_append, gateCount_append, gateCount_gateList, gateCount_gate]
  simp
  omega

/-- The word has two CNOTs per nonzero entry of `p` and one rotation per row. -/
theorem zNetworkWord_size {n k : ℕ} (p : Fin k → F2Vec n) (θ : Fin k → ℝ) :
    Size (zNetworkWord n k p θ) = 2 * edgeCount p + k := by
  induction k with
  | zero => simp [zNetworkWord, edgeCount, Size]
  | succ k ih =>
      rw [zNetworkWord, size_append, ih, rowWord_size, rowEdges_length, edgeCount_succ]
      have hd : (∑ i : Fin k,
          (Finset.univ.filter (fun j => p i.succ j = 1)).card) =
          edgeCount (fun i => p i.succ) := rfl
      rw [hd]
      omega

/-- The word contains exactly as many instructions as gates. -/
theorem zNetworkWord_gateCount {n k : ℕ} (p : Fin k → F2Vec n) (θ : Fin k → ℝ) :
    GateCount (zNetworkWord n k p θ) = 2 * edgeCount p + k := by
  induction k with
  | zero => simp [zNetworkWord, edgeCount]
  | succ k ih =>
      rw [zNetworkWord, gateCount_append, ih, rowWord_gateCount, rowEdges_length, edgeCount_succ]
      have hd : (∑ i : Fin k,
          (Finset.univ.filter (fun j => p i.succ j = 1)).card) =
          edgeCount (fun i => p i.succ) := rfl
      rw [hd]
      omega

/-- The word has at most `2 * (n * k) + k` instructions, a polynomial resource bound in the
number of data coordinates and rows. -/
theorem zNetworkWord_size_le {n k : ℕ} (p : Fin k → F2Vec n) (θ : Fin k → ℝ) :
    Size (zNetworkWord n k p θ) ≤ 2 * (n * k) + k := by
  rw [zNetworkWord_size]
  have h := edgeCount_le p
  omega

/-- The denotation of a list of explicit gates is the reversed matrix product. -/
theorem denote_gateList {I : Type*} [Fintype I] [DecidableEq I]
    (l : List (Matrix I I ℂ)) :
    Denote (1 : Matrix I I ℂ) (l.map Step.gate) = l.reverse.prod := by
  induction l with
  | nil => simp [Denote]
  | cons g l ih =>
      rw [List.map_cons, denote_gate, ih, List.reverse_cons, List.prod_append]
      simp

/-- One row of the word denotes the row operator: the conjugated ancilla rotation. -/
theorem rowWord_denote {n : ℕ} (p : F2Vec n) (θ : ℝ) :
    Denote (1 : Matrix (DataBus n) (DataBus n) ℂ) (rowWord p θ) = rowOperator p θ := by
  rw [rowWord, denote_append, denote_append]
  simp only [denote_gate, denote_nil, denote_gateList, ladder, rowOperator]
  simp

/-- The whole word denotes the product of the row operators, which is diagonal in the
data-ancilla basis. -/
theorem zNetworkWord_denote {n k : ℕ} (p : Fin k → F2Vec n) (θ : Fin k → ℝ) :
    Denote (1 : Matrix (DataBus n) (DataBus n) ℂ) (zNetworkWord n k p θ) =
      Matrix.diagonal (fun a : DataBus n =>
        ∏ i, zCoeff (θ i) (decide (a.2 + dot (p i) a.1 = 0))) := by
  induction k with
  | zero => simp [zNetworkWord, Denote]
  | succ k ih =>
      rw [zNetworkWord, denote_append, ih, rowWord_denote, rowOperator_eq_diagonal,
        Matrix.diagonal_mul_diagonal]
      congr 1
      funext a
      rw [Fin.prod_univ_succ]

/-- On the ancilla-zero sector the word multiplies by the product of the character multipliers
`zCoeff (θ i) (dot (p i) x = 0)`, the eigenvalue product of
`Qatlib.Papers.Instantaneous08.MainResults.ConstantAction.circuitOp_char`. -/
theorem zNetworkWord_mulVec_zero {n k : ℕ} (p : Fin k → F2Vec n) (θ : Fin k → ℝ)
    (ψ : DataBus n → ℂ) (x : F2Vec n) :
    ((Denote (1 : Matrix (DataBus n) (DataBus n) ℂ) (zNetworkWord n k p θ)) *ᵥ ψ) (x, 0) =
      (∏ i, zCoeff (θ i) (decide (dot (p i) x = 0))) * ψ (x, 0) := by
  rw [zNetworkWord_denote, Matrix.mulVec_diagonal]
  simp

end Qatlib.Papers.Instantaneous08.MainResults
