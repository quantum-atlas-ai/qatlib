/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

/-!
# Resource counting for structured state preparation

Combinatorial core of Supplementary Sections III.2–III.5 (Corollaries S5–S7) of
*Harnessing problem structure for end-to-end quantum state preparation*
(arXiv:2609.40105v1).

The declarations here isolate the counting steps that every family construction
shares.  Each construction combines a decomposition tree with a per-block cost
that is linear in the register size `n` and in the number of interface labels or
records attached to the block:

* `nodes_le_two_mul_leaves`: a binary tree with `S` leaves has fewer than
  `2S` nodes (`supportTreeCost_le`), giving the `O(S n)` cost of the sparse
  support-tree construction (Corollary S5).
* `givens_le_edges`: the number of Givens rotations needed by the decision
  diagram, `∑_{w ≠ root} max(indeg w - 1, 0)`, is at most the number `|E|` of
  edges (Eq. (S34)), giving the `O(|E| n)` cost of Corollary S6.
* `depthSum_le`, `gateSum_le`: a balanced Schmidt tree whose layers have widths
  `m_j` and rank at most `r` needs depth `∑ m_j` and at most `r² ∑ m_j` gates
  (Corollary S7), hence `O(n)` depth and `O(n log n)` gates for `r = O(1)`.
* `chainCost_le`: a stack of `S` support states connected by `S - 1` local
  updates costs `O(S n)` (Corollary S5).
-/

namespace Qatlib.Papers.ProbStructure26.StatePrep

open Finset

/-- A binary decomposition tree, the skeleton of every recursive family
construction. -/
inductive BTree : Type
  | leaf : BTree
  | node : BTree → BTree → BTree
  deriving Repr

namespace BTree

/-- Number of leaves (interface records) of a decomposition tree. -/
def leaves : BTree → ℕ
  | leaf => 1
  | node l r => leaves l + leaves r

/-- Number of internal and leaf nodes of a decomposition tree. -/
def nodes : BTree → ℕ
  | leaf => 1
  | node l r => nodes l + nodes r + 1

/-- A binary tree with `S` leaves has `2S - 1` nodes; in particular fewer than
`2S` nodes (`nodes + 1 ≤ 2 * leaves`). -/
theorem nodes_succ_le_two_mul_leaves (t : BTree) :
    nodes t + 1 ≤ 2 * leaves t := by
  induction t with
  | leaf => simp [nodes, leaves]
  | node l r ihl ihr =>
      simp only [nodes, leaves]
      omega

end BTree

/-- Per-node cost of one recursive update on a register of size `n`: a constant
number of local updates of width `n`.  The sparse-tree construction pays this
for every node of the decomposition tree. -/
def supportTreeCost (t : BTree) (n : ℕ) : ℕ := BTree.nodes t * n

/-- Corollary S5: the support-tree construction costs `O(S n)` gates, where `S`
is the number of sparse support strings (leaves). -/
theorem supportTreeCost_le (t : BTree) (n : ℕ) :
    supportTreeCost t n ≤ 2 * BTree.leaves t * n := by
  unfold supportTreeCost
  have h := BTree.nodes_succ_le_two_mul_leaves t
  nlinarith

/-- Cost of a chain of `S` support states joined by `S - 1` local updates, each
of width `n`. -/
def chainCost (S n : ℕ) : ℕ := S * n

/-- Corollary S5, chain form: `S` support states cost at most `S n`, which is
`O(S n)`. -/
theorem chainCost_le (S n : ℕ) : chainCost S n ≤ S * n := by
  unfold chainCost
  exact le_rfl

/-- A levelized decision diagram: `V` vertices, `root : Fin V`, and the
in-degree function `indeg`.  The number of edges is `∑_w indeg w`. -/
structure DecisionDiagram (V : ℕ) where
  root : Fin V
  indeg : Fin V → ℕ

/-- Number of edges of the diagram. -/
def DecisionDiagram.edgeCount {V : ℕ} (Q : DecisionDiagram V) : ℕ :=
  ∑ w, Q.indeg w

/-- Givens count `∑_{w ≠ root} max(indeg w - 1, 0)` of Eq. (S34). -/
def DecisionDiagram.givensCount {V : ℕ} (Q : DecisionDiagram V) : ℕ :=
  ∑ w ∈ Finset.univ.erase Q.root, max (Q.indeg w - 1) 0

/-- Eq. (S34): the Givens count of a decision diagram is at most its number of
edges, since `max(indeg w - 1, 0) ≤ indeg w` at every non-root vertex. -/
theorem givens_le_edges {V : ℕ} (Q : DecisionDiagram V) :
    Q.givensCount ≤ Q.edgeCount := by
  unfold DecisionDiagram.givensCount DecisionDiagram.edgeCount
  calc (∑ w ∈ Finset.univ.erase Q.root, max (Q.indeg w - 1) 0)
      ≤ ∑ w ∈ Finset.univ.erase Q.root, Q.indeg w := by
        apply Finset.sum_le_sum
        intro w _
        exact max_le (Nat.sub_le _ _) (Nat.zero_le _)
    _ ≤ ∑ w, Q.indeg w := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun x _ _ => Nat.zero_le _)

/-- Per-update cost on a register of size `n` for a decision-diagram step. -/
def diagramCost {V : ℕ} (Q : DecisionDiagram V) (n : ℕ) : ℕ :=
  Q.givensCount * n

/-- Corollary S6: the decision-diagram construction costs `O(|E| n)` gates. -/
theorem diagramCost_le {V : ℕ} (Q : DecisionDiagram V) (n : ℕ) :
    diagramCost Q n ≤ Q.edgeCount * n := by
  unfold diagramCost
  exact Nat.mul_le_mul_right n (givens_le_edges Q)

/-- Layer widths of a balanced Schmidt tree.  `m` is the list of layer widths;
the construction processes one Schmidt rank per layer. -/
def layerDepth {L : ℕ} (m : Fin L → ℕ) : ℕ := ∑ j, m j

/-- Layer gate count: each layer with width `m_j` and rank at most `r` costs
`r² m_j` two-level gates. -/
def layerGates {L : ℕ} (r : ℕ) (m : Fin L → ℕ) : ℕ := ∑ j, r * r * m j

/-- Corollary S7, depth: the total depth of a balanced Schmidt tree is the sum
of the layer widths. -/
theorem layerDepth_eq {L : ℕ} (m : Fin L → ℕ) : layerDepth m = ∑ j, m j := rfl

/-- Corollary S7: the depth is at most the register size `n` whenever the layer
widths sum to at most `n`. -/
theorem depthSum_le {L : ℕ} (m : Fin L → ℕ) (n : ℕ) (h : ∑ j, m j ≤ n) :
    layerDepth m ≤ n := by
  rw [layerDepth_eq]
  exact h

/-- Corollary S7, gates: with rank at most `r` at every layer the gate count is
`r²` times the total width, hence `O(n)` for fixed `r`. -/
theorem gateSum_le {L : ℕ} (r : ℕ) (m : Fin L → ℕ) (n : ℕ)
    (h : ∑ j, m j ≤ n) :
    layerGates r m ≤ r * r * n := by
  unfold layerGates
  rw [← Finset.mul_sum]
  exact Nat.mul_le_mul_left (r * r) h

/-- A tree that splits into at most `Λ` interface labels per block and has `N`
blocks needs at most `Λ N` interface records, the form in which the paper's
`n^{d+1}` record count is used. -/
def interfaceRecords (Λ N : ℕ) : ℕ := Λ * N

/-- The interface-record count is monotone in the number of blocks. -/
theorem interfaceRecords_le (Λ N M : ℕ) (h : N ≤ M) :
    interfaceRecords Λ N ≤ interfaceRecords Λ M := by
  unfold interfaceRecords
  exact Nat.mul_le_mul_left Λ h

end Qatlib.Papers.ProbStructure26.StatePrep
