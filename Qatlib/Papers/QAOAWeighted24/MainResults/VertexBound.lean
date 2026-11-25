/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-!
# The common-neighbor obstruction to Lemma 4

In a complete bipartite graph, many neighbors can lead to the same
second vertex even though there are no triangles. The two-step
count per starting vertex requires separate branches. Pairwise
disjoint neighbor sets after erasing the start suffice for the count.
-/

set_option autoImplicit false

open scoped BigOperators Classical
open SimpleGraph

namespace Qatlib.Papers.QAOAWeighted24.MainResults

/-- The complete bipartite graph with two parts of size four is
triangle-free and four-regular, but has fewer than twelve vertices. -/
theorem k44_violates_vertex_bound :
    let G := completeBipartiteGraph (Fin 4) (Fin 4)
    G.CliqueFree 3 ∧ (∀ v, G.degree v = 4) ∧
      Fintype.card (Fin 4 ⊕ Fin 4) < 3 * 4 := by
  dsimp only
  have hcolor : (completeBipartiteGraph (Fin 4) (Fin 4)).Colorable 2 := by
    simpa using (CompleteBipartiteGraph.bicoloring (Fin 4) (Fin 4)).colorable
  refine ⟨hcolor.cliqueFree (by decide), ?_, by decide⟩
  have hleft (v : Fin 4) :
      (completeBipartiteGraph (Fin 4) (Fin 4)).neighborFinset (Sum.inl v) =
        Finset.univ.map Function.Embedding.inr := by
    ext x
    cases x <;> simp [SimpleGraph.mem_neighborFinset, Finset.mem_map]
  have hright (v : Fin 4) :
      (completeBipartiteGraph (Fin 4) (Fin 4)).neighborFinset (Sum.inr v) =
        Finset.univ.map Function.Embedding.inl := by
    ext x
    cases x <;> simp [SimpleGraph.mem_neighborFinset, Finset.mem_map]
  intro v
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  cases v with
  | inl v => rw [hleft, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  | inr v => rw [hright, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- Pairwise disjoint second-neighbor sets at one vertex suffice for
the quadratic vertex bound. In a simple graph this excludes four
cycles through the chosen vertex. -/
theorem vertex_card_ge_of_disjoint {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) (u : V)
    (hreg : ∀ v, G.degree v = D + 1)
    (hdisjoint : (↑(G.neighborFinset u) : Set V).PairwiseDisjoint
      (fun v => (G.neighborFinset v).erase u)) :
    D * (D + 1) ≤ Fintype.card V := by
  have hcount (v : V) (hv : v ∈ G.neighborFinset u) :
      ((G.neighborFinset v).erase u).card = D := by
    have hu : u ∈ G.neighborFinset v :=
      (G.mem_neighborFinset v u).2 ((G.mem_neighborFinset u v).1 hv).symm
    rw [Finset.card_erase_of_mem hu, SimpleGraph.card_neighborFinset_eq_degree, hreg]
    omega
  let reached := (G.neighborFinset u).biUnion (fun v => (G.neighborFinset v).erase u)
  have hall : reached.card = (D + 1) * D := by
    change ((G.neighborFinset u).biUnion _).card = _
    rw [Finset.card_biUnion hdisjoint]
    calc
      _ = ∑ _v ∈ G.neighborFinset u, D := Finset.sum_congr rfl hcount
      _ = _ := by
        simp [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, hreg]
  rw [Nat.mul_comm, ← hall]
  exact Finset.card_le_univ reached

end Qatlib.Papers.QAOAWeighted24.MainResults
