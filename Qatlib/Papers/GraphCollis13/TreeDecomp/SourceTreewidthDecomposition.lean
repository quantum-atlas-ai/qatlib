/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Range
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 1 — tree decomposition into bounded vertex subsets

Fixed arXiv:1305.1021v1, §2 ("Graph collision based on treewidth"), Lemma 1, page 3.

Source statement: for a graph `G = (V,E)` with treewidth `t` there exists a
decomposition into vertex subsets `W = (W_i)`, `W_i ⊆ V`, with
`|W| = ⌈(2n − 2t − 1)/t⌉`, `|W_i| ≤ 2t + 1` for every `i`, and such that every edge
`(v,w) ∈ E` is contained in some `W_i`.

The formal development fixes the standard smooth-tree-decomposition vocabulary:
all bags have `t+1` vertices and adjacent bags intersect in exactly `t` vertices.
The paper's proof traverses the decomposition tree like a maze (each tree edge
twice), slices the resulting vertex sequence of length `2n−2t−1` into blocks of
length `t`, and sets `W_i` to the union of the bags in block `i`.  The two local
cardinality facts of that construction are proved below.  Scope note: the maze
traversal and the standard fact `|I| = |V| − t` for a smooth decomposition
(Bodlaender [4]) are outside the scope of this file.  The final statement is a
`Prop`-valued definition whose proof is not formalised.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.GraphCollis13.TreeDecomp.TreewidthDecomposition

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A smooth tree decomposition of a finite graph `G` on `m` tree nodes, all bags of
size `t + 1`, with adjacent tree nodes meeting in exactly `t` vertices.  The usual
connectedness condition of tree decompositions is not needed for the slicing
argument and is omitted; every smooth tree decomposition of the paper satisfies
this structure after reindexing its node set by `Fin m`. -/
structure SmoothTreeDecomposition (G : SimpleGraph V) (t m : ℕ) where
  /-- The decomposition tree. -/
  tree : SimpleGraph (Fin m)
  /-- The decomposition tree is a tree. -/
  isTree : tree.IsTree
  /-- The bag of a tree node. -/
  bag : Fin m → Finset V
  /-- Every vertex lies in some bag. -/
  covers_vertices : ∀ v : V, ∃ i : Fin m, v ∈ bag i
  /-- Every edge is contained in some bag. -/
  covers_edges : ∀ ⦃v w : V⦄, G.Adj v w → ∃ i : Fin m, v ∈ bag i ∧ w ∈ bag i
  /-- Smoothness: all bags have `t + 1` vertices. -/
  smooth_size : ∀ i : Fin m, (bag i).card = t + 1
  /-- Smoothness: adjacent bags meet in exactly `t` vertices. -/
  smooth_inter : ∀ i j : Fin m, tree.Adj i j → (bag i ∩ bag j).card = t

/-- **Treewidth at most `t`** in the smooth-decomposition vocabulary used for the
paper's Lemma 1.  This is implied by the usual treewidth bound through the standard
smoothing transformation (the paper quotes Bodlaender [4]). -/
def HasTreewidthAtMost (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ m : ℕ, Nonempty (SmoothTreeDecomposition G t m)

/-- Along a walk in a smooth decomposition, the union of `k ≥ 1` consecutive bags
has at most `t + k` vertices.  This is the cardinality estimate underlying the
paper's `|W_i| ≤ 2t + 1` claim: a block of `t` consecutive bags spans at most
`t + t = 2t` vertices. -/
theorem union_consecutive_bags_card_le {G : SimpleGraph V} {t m : ℕ}
    (D : SmoothTreeDecomposition G t m) (u : ℕ → Fin m)
    (hadj : ∀ j : ℕ, D.tree.Adj (u j) (u (j + 1))) (k : ℕ) (hk : 1 ≤ k) :
    ((Finset.range k).biUnion (fun j => D.bag (u j))).card ≤ t + k := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      have hsingle : (Finset.range 1).biUnion (fun j => D.bag (u j)) = D.bag (u 0) := by
        simp
      rw [hsingle, D.smooth_size (u 0)]
    · have hrec : ((Finset.range k).biUnion (fun j => D.bag (u j))).card ≤ t + k := ih hkpos
      have hprev_adj : D.tree.Adj (u (k - 1)) (u k) := by
        have h := hadj (k - 1)
        rwa [Nat.sub_add_cancel hkpos] at h
      have hdiff_card : (D.bag (u k) \ D.bag (u (k - 1))).card ≤ 1 := by
        have hsize : (D.bag (u k)).card = t + 1 := D.smooth_size (u k)
        have hinter : (D.bag (u k) ∩ D.bag (u (k - 1))).card = t := by
          rw [Finset.inter_comm]
          exact D.smooth_inter (u (k - 1)) (u k) hprev_adj
        have hcs := Finset.card_sdiff (s := D.bag (u (k - 1))) (t := D.bag (u k))
        rw [hcs, Finset.inter_comm, hinter, hsize]
        omega
      have hsub : (Finset.range (k + 1)).biUnion (fun j => D.bag (u j)) ⊆
          (Finset.range k).biUnion (fun j => D.bag (u j)) ∪
            (D.bag (u k) \ D.bag (u (k - 1))) := by
        intro x hx
        rw [Finset.mem_biUnion] at hx
        obtain ⟨j, hj, hxj⟩ := hx
        rw [Finset.mem_range] at hj
        rw [Finset.mem_union]
        rcases lt_or_ge j k with hjk | hjk
        · exact Or.inl (Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hjk, hxj⟩)
        · have hj_eq : j = k := by omega
          subst j
          by_cases hprev : x ∈ D.bag (u (k - 1))
          · exact Or.inl (Finset.mem_biUnion.mpr
              ⟨k - 1, Finset.mem_range.mpr (by omega), hprev⟩)
          · exact Or.inr (Finset.mem_sdiff.mpr ⟨hxj, hprev⟩)
      calc
        ((Finset.range (k + 1)).biUnion (fun j => D.bag (u j))).card
            ≤ (((Finset.range k).biUnion (fun j => D.bag (u j))) ∪
                (D.bag (u k) \ D.bag (u (k - 1)))).card := Finset.card_le_card hsub
        _ ≤ ((Finset.range k).biUnion (fun j => D.bag (u j))).card +
              (D.bag (u k) \ D.bag (u (k - 1))).card := Finset.card_union_le _ _
        _ ≤ (t + k) + 1 := by omega
        _ = t + (k + 1) := by ring

/-- A traversal of the decomposition tree that visits every node induces, for each
graph edge, a block whose union of bags contains both endpoints.  This is the
edge-coverage half of the paper's Lemma 1 proof. -/
theorem edge_mem_union_of_visit {G : SimpleGraph V} {t m : ℕ}
    (D : SmoothTreeDecomposition G t m) (u : ℕ → Fin m)
    (hvisit : ∀ i : Fin m, ∃ j : ℕ, u j = i) {v w : V} (h : G.Adj v w) :
    ∃ j : ℕ, v ∈ D.bag (u j) ∧ w ∈ D.bag (u j) := by
  obtain ⟨i, hv, hw⟩ := D.covers_edges h
  obtain ⟨j, rfl⟩ := hvisit i
  exact ⟨j, hv, hw⟩

/-- **Lemma 1 (arXiv:1305.1021v1, page 3).**  For a graph on `n` vertices with
treewidth `t > 0` there is a family `W` of vertex subsets, indexed by
`⌈(2n − 2t − 1)/t⌉` blocks, such that every block has at most `2t + 1` vertices and
every edge of the graph is contained in some block.

Proof route (paper): take a smooth tree decomposition with `n − t` nodes, traverse
its tree like a maze (every edge twice) to obtain a node sequence of length
`2n − 2t − 1`, slice the sequence into `t`-blocks and merge the bags of each block.

Scope note: this file proves the two local cardinality steps
(`union_consecutive_bags_card_le`, `edge_mem_union_of_visit`).  The existence of
the maze traversal (an Euler tour of length `2|E_T| + 1`) and the
smooth-decomposition count `|I| = |V| − t` are outside its scope.
The traversal can be obtained by depth-first search on the tree, and the count
`m = Fintype.card V - t` follows from the standard incidence identity
`Σ_i |X_i| − Σ_{edges of T} |X_i ∩ X_j| = |V|`. -/
def lemma1_treewidth_decomposition (G : SimpleGraph V) (t : ℕ) (ht : 0 < t)
    (h : HasTreewidthAtMost G t) : Prop :=
    ∃ (mW : ℕ) (W : Fin mW → Finset V),
      mW = Nat.ceil (((2 * (Fintype.card V : ℝ)) - 2 * (t : ℝ) - 1) / (t : ℝ)) ∧
      (∀ i : Fin mW, (W i).card ≤ 2 * t + 1) ∧
      (∀ ⦃v w : V⦄, G.Adj v w → ∃ i : Fin mW, v ∈ W i ∧ w ∈ W i)

end Qatlib.Papers.GraphCollis13.TreeDecomp.TreewidthDecomposition
