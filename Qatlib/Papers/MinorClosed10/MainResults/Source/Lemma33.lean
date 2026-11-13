/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MinorClosed10.MainResults.Model.PaperObjects

set_option backward.isDefEq.respectTransparency false

/-!
# Strict Decrease of the Internal-Edge Count Under Two-Path Splitting

This module formalizes Lemma 3.3 of Childs and Kothari showing that deleting an
internal edge `(u, v)` of a graph `G` and attaching two disjoint paths at `u`
and `v` strictly decreases the internal-edge parameter `β`.

## Main statements

* `lemma33`: Lemma 3.3, `beta (twoPathSplitSum G u v n₁ n₂) < beta G` whenever
  `IsInternalEdge G u v`.

## References

* [Childs and Kothari, 2012][ChildsKothari2012], Section 3, Lemma 3.3, p. 10.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MinorClosed10.MainResults.Source

open Qatlib.Papers.MinorClosed10.MainResults
open scoped Classical

private def splitDepth {k n₁ n₂ : ℕ} : ((Fin k ⊕ Fin n₁) ⊕ Fin n₂) → ℕ
  | .inl (.inl _) => 0
  | .inl (.inr i) => i.val + 1
  | .inr i => i.val + 1

private def splitProjection {k n₁ n₂ : ℕ} (u v : Fin k) :
    ((Fin k ⊕ Fin n₁) ⊕ Fin n₂) → Fin k
  | .inl (.inl w) => w
  | .inl (.inr _) => u
  | .inr _ => v

private def splitNeighborImage {k n₁ n₂ : ℕ} (u v : Fin k) :
    ((Fin k ⊕ Fin n₁) ⊕ Fin n₂) → Fin k
  | .inl (.inl w) => w
  | .inl (.inr _) => v
  | .inr _ => u

-- Each attachment replaces a deleted neighbor, giving an injection of neighbor sets.
private theorem split_old_degree_le {k : ℕ} (G : SimpleGraph (Fin k))
    {u v : Fin k} (huv : G.Adj u v) (n₁ n₂ : ℕ) (w : Fin k) :
    (twoPathSplitSum G u v n₁ n₂).degree (.inl (.inl w)) ≤ G.degree w := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_le_card_of_injOn (splitNeighborImage u v)
  · intro x hx
    rcases x with ((x | x) | x) <;>
      simp_all [twoPathSplitSum, SimpleGraph.fromRel_adj, splitNeighborImage] <;>
      first | exact huv.symm | tauto
  · intro x hx y hy hxy
    have hne := huv.ne
    rcases x with ((x | x) | x) <;> rcases y with ((y | y) | y) <;>
      simp_all [twoPathSplitSum, SimpleGraph.fromRel_adj, splitNeighborImage,
        Fin.ext_iff]

private theorem split_new_neighbor_depth_inj {k n₁ n₂ : ℕ}
    (G : SimpleGraph (Fin k)) (u v : Fin k)
    {z : (Fin k ⊕ Fin n₁) ⊕ Fin n₂} (hz : splitDepth z ≠ 0)
    {x y : (Fin k ⊕ Fin n₁) ⊕ Fin n₂}
    (hx : (twoPathSplitSum G u v n₁ n₂).Adj z x)
    (hy : (twoPathSplitSum G u v n₁ n₂).Adj z y)
    (hxy : splitDepth x = splitDepth y) : x = y := by
  rcases z with ((z | z) | z) <;>
    rcases x with ((x | x) | x) <;> rcases y with ((y | y) | y) <;>
    simp_all [twoPathSplitSum, SimpleGraph.fromRel_adj, splitDepth, Fin.ext_iff] <;> omega

private theorem split_new_degree_le {k n₁ n₂ : ℕ} (G : SimpleGraph (Fin k))
    (u v : Fin k) {z : (Fin k ⊕ Fin n₁) ⊕ Fin n₂} (hz : splitDepth z ≠ 0) :
    (twoPathSplitSum G u v n₁ n₂).degree z ≤ 2 := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  refine le_trans (Finset.card_le_card_of_injOn splitDepth
    (t := {splitDepth z - 1, splitDepth z + 1}) ?_ ?_) Finset.card_le_two
  · intro x hx
    rcases z with ((z | z) | z) <;> rcases x with ((x | x) | x) <;>
      simp_all [twoPathSplitSum, SimpleGraph.fromRel_adj, splitDepth] <;> omega
  · intro x hx y hy hxy
    exact split_new_neighbor_depth_inj G u v hz
      (by simpa using hx) (by simpa using hy) hxy

private def splitTail {k n₁ n₂ : ℕ}
    (z x : (Fin k ⊕ Fin n₁) ⊕ Fin n₂) : Prop :=
  match z, x with
  | .inl (.inr i), .inl (.inr j) => i.val ≤ j.val
  | .inr i, .inr j => i.val ≤ j.val
  | _, _ => False

-- A path suffix contains only added vertices and has a unique boundary edge.
private theorem split_tail_depth {k n₁ n₂ : ℕ}
    {z x : (Fin k ⊕ Fin n₁) ⊕ Fin n₂} (h : splitTail z x) :
    splitDepth z ≤ splitDepth x ∧ splitDepth x ≠ 0 := by
  rcases z with ((z | z) | z) <;> rcases x with ((x | x) | x) <;>
    simp_all [splitTail, splitDepth]

private theorem split_tail_boundary {k n₁ n₂ : ℕ} (G : SimpleGraph (Fin k))
    (u v : Fin k) {z x y : (Fin k ⊕ Fin n₁) ⊕ Fin n₂}
    (hxy : (twoPathSplitSum G u v n₁ n₂).Adj x y)
    (hx : ¬ splitTail z x) (hy : splitTail z y) :
    y = z ∧ splitDepth x + 1 = splitDepth z := by
  rcases z with ((z | z) | z) <;>
    rcases x with ((x | x) | x) <;> rcases y with ((y | y) | y) <;>
    simp_all [twoPathSplitSum, SimpleGraph.fromRel_adj, splitTail,
      splitDepth, Fin.ext_iff] <;> omega

private theorem reachable_invariant {V : Type} {H : SimpleGraph V}
    (P : V → Prop) (hP : ∀ x y, H.Adj x y → (P x ↔ P y))
    {x y : V} (hxy : H.Reachable x y) : P x ↔ P y := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => rfl
  | cons h _ ih => exact (hP _ _ h).trans ih

-- Deleting the boundary edge separates a suffix with no vertex of degree at least three.
private theorem split_not_internal_of_depth_lt {k n₁ n₂ : ℕ}
    (G : SimpleGraph (Fin k)) (u v : Fin k)
    {a b : (Fin k ⊕ Fin n₁) ⊕ Fin n₂}
    (hab : splitDepth a < splitDepth b) :
    ¬ IsInternalEdge (twoPathSplitSum G u v n₁ n₂) a b := by
  intro hi
  obtain ⟨hadj, hinter⟩ := hi
  have hb : splitDepth b ≠ 0 := by omega
  have hbb : splitTail b b := by
    rcases b with ((b | b) | b) <;> simp_all [splitTail, splitDepth]
  have hab' : ¬ splitTail b a := fun h => (split_tail_depth h).1.not_gt hab
  have hboundary := split_tail_boundary G u v hadj hab' hbb
  have cross : ∀ x y, (twoPathSplitSum G u v n₁ n₂).Adj x y →
      ¬ splitTail b x → splitTail b y → Sym2.mk x y = Sym2.mk a b := by
    intro c d hcd hc hd
    obtain ⟨hdb, hdepth⟩ := split_tail_boundary G u v hcd hc hd
    subst d
    have hca : c = a := split_new_neighbor_depth_inj G u v hb
      hcd.symm hadj.symm (by omega)
    simp [hca]
  have hcut : ∀ x y,
      ((twoPathSplitSum G u v n₁ n₂).deleteEdges {Sym2.mk a b}).Adj x y →
        (splitTail b x ↔ splitTail b y) := by
    intro x y hxy
    obtain ⟨hxy, hne⟩ := SimpleGraph.deleteEdges_adj.mp hxy
    simp only [Set.mem_singleton_iff] at hne
    constructor
    · intro hx
      by_contra hy
      exact hne (Sym2.eq_swap.trans (cross y x hxy.symm hy hx))
    · intro hy
      by_contra hx
      exact hne (cross x y hxy hx hy)
  rcases hinter with hcycle | ⟨_, ⟨y, hby, hy⟩⟩
  · exact hab' ((reachable_invariant (splitTail b) hcut hcycle).mpr hbb)
  · have htail := (reachable_invariant (splitTail b) hcut hby).mp hbb
    have hdegree := split_new_degree_le G u v (split_tail_depth htail).2
    omega

private theorem internal_edge_symm {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a b : V} (h : IsInternalEdge G a b) :
    IsInternalEdge G b a := by
  rcases h with ⟨hab, hcycle | ⟨ha, hb⟩⟩
  · exact ⟨hab.symm, Or.inl (by simpa [Sym2.eq_swap] using hcycle.symm)⟩
  · exact ⟨hab.symm, Or.inr (by simpa [Sym2.eq_swap] using And.intro hb ha)⟩

private theorem split_internal_endpoints {k n₁ n₂ : ℕ} (G : SimpleGraph (Fin k))
    (u v : Fin k) {a b : (Fin k ⊕ Fin n₁) ⊕ Fin n₂}
    (h : IsInternalEdge (twoPathSplitSum G u v n₁ n₂) a b) :
    ∃ x y : Fin k, a = .inl (.inl x) ∧ b = .inl (.inl y) := by
  have hab : ¬ splitDepth a < splitDepth b :=
    fun hlt => split_not_internal_of_depth_lt G u v hlt h
  have hba : ¬ splitDepth b < splitDepth a :=
    fun hlt => split_not_internal_of_depth_lt G u v hlt (internal_edge_symm h)
  have heq : splitDepth a = splitDepth b := by omega
  have hadj := h.1
  rcases a with ((a | a) | a) <;> rcases b with ((b | b) | b)
  · exact ⟨a, b, rfl, rfl⟩
  all_goals simp_all [twoPathSplitSum, SimpleGraph.fromRel_adj, splitDepth]

private theorem split_old_adj {k n₁ n₂ : ℕ} (G : SimpleGraph (Fin k))
    (u v a b : Fin k) :
    (twoPathSplitSum G u v n₁ n₂).Adj (.inl (.inl a)) (.inl (.inl b)) ↔
      G.Adj a b ∧ Sym2.mk a b ≠ Sym2.mk u v := by
  have hab : G.Adj a b → a ≠ b := SimpleGraph.Adj.ne
  have hba : G.Adj b a ↔ G.Adj a b := G.adj_comm b a
  simp only [twoPathSplitSum, SimpleGraph.fromRel_adj, ne_eq, Sum.inl.injEq, Sym2.eq_iff]
  tauto

private theorem reachable_map_of_adj {V W : Type} {H : SimpleGraph V}
    {G : SimpleGraph W} (f : V → W)
    (hf : ∀ x y, H.Adj x y → G.Reachable (f x) (f y))
    {x y : V} (h : H.Reachable x y) : G.Reachable (f x) (f y) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact .rfl
  | cons hadj _ ih => exact (hf _ _ hadj).trans ih

-- Collapsing each dangling path to its root preserves edge-deleted reachability.
private theorem split_reachable_projection {k n₁ n₂ : ℕ}
    (G : SimpleGraph (Fin k)) (u v a b : Fin k)
    {x y : (Fin k ⊕ Fin n₁) ⊕ Fin n₂}
    (h : ((twoPathSplitSum G u v n₁ n₂).deleteEdges
      {Sym2.mk (.inl (.inl a)) (.inl (.inl b))}).Reachable x y) :
    (G.deleteEdges {Sym2.mk a b}).Reachable
      (splitProjection u v x) (splitProjection u v y) := by
  apply reachable_map_of_adj (splitProjection u v) (h := h)
  intro c d hcd
  obtain ⟨hadj, hne⟩ := SimpleGraph.deleteEdges_adj.mp hcd
  rcases c with ((c | c) | c) <;> rcases d with ((d | d) | d)
  · apply SimpleGraph.Adj.reachable
    have hold := (split_old_adj G u v c d).mp hadj
    simpa [SimpleGraph.deleteEdges_adj, splitProjection, Sym2.eq_iff] using
      And.intro hold.1 hne
  all_goals
    simp_all [twoPathSplitSum, SimpleGraph.fromRel_adj, splitProjection]

private theorem split_internal_old {k n₁ n₂ : ℕ} (G : SimpleGraph (Fin k))
    {u v : Fin k} (huv : G.Adj u v) {a b : Fin k}
    (h : IsInternalEdge (twoPathSplitSum G u v n₁ n₂)
      (.inl (.inl a)) (.inl (.inl b))) :
    IsInternalEdge G a b ∧ Sym2.mk a b ≠ Sym2.mk u v := by
  have hold := (split_old_adj G u v a b).mp h.1
  refine ⟨⟨hold.1, ?_⟩, hold.2⟩
  rcases h.2 with hcycle | ⟨⟨x, hax, hx⟩, ⟨y, hby, hy⟩⟩
  · exact Or.inl (split_reachable_projection G u v a b hcycle)
  · have high : ∀ z : (Fin k ⊕ Fin n₁) ⊕ Fin n₂,
        3 ≤ (twoPathSplitSum G u v n₁ n₂).degree z →
          3 ≤ G.degree (splitProjection u v z) := by
      intro z hz
      by_cases hzero : splitDepth z = 0
      · rcases z with ((z | z) | z) <;> simp_all [splitDepth, splitProjection]
        exact hz.trans (split_old_degree_le G huv n₁ n₂ z)
      · have := split_new_degree_le G u v hzero
        omega
    exact Or.inr ⟨⟨_, split_reachable_projection G u v a b hax, high x hx⟩,
      ⟨_, split_reachable_projection G u v a b hby, high y hy⟩⟩

/-- Lemma 3.3: splitting an internal edge into two attached paths strictly
decreases `β`. -/
theorem lemma33 {k : ℕ} (G : SimpleGraph (Fin k)) {u v : Fin k}
    (h : IsInternalEdge G u v) (n₁ n₂ : ℕ) :
    beta (twoPathSplitSum G u v n₁ n₂) < beta G := by
  classical
  let old : Fin k ↪ ((Fin k ⊕ Fin n₁) ⊕ Fin n₂) :=
    ⟨fun w => .inl (.inl w), by intro x y hxy; simpa using hxy⟩
  let original := G.edgeFinset.filter
    (fun e => ∃ a b, e = Sym2.mk a b ∧ IsInternalEdge G a b)
  let split := (twoPathSplitSum G u v n₁ n₂).edgeFinset.filter
    (fun e => ∃ a b, e = Sym2.mk a b ∧
      IsInternalEdge (twoPathSplitSum G u v n₁ n₂) a b)
  have hmem : Sym2.mk u v ∈ original :=
    Finset.mem_filter.mpr ⟨by simpa using h.1, u, v, rfl, h⟩
  have hsub : split ⊆ (original.erase (Sym2.mk u v)).map old.sym2Map := by
    intro e he
    obtain ⟨a, b, rfl, hab⟩ := (Finset.mem_filter.mp he).2
    obtain ⟨x, y, rfl, rfl⟩ := split_internal_endpoints G u v hab
    have htransfer := split_internal_old G h.1 hab
    apply Finset.mem_map.mpr
    refine ⟨Sym2.mk x y, Finset.mem_erase.mpr ⟨htransfer.2, ?_⟩, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨by simpa using htransfer.1.1, x, y, rfl, htransfer.1⟩
  calc
    beta (twoPathSplitSum G u v n₁ n₂) = split.card := rfl
    _ ≤ ((original.erase (Sym2.mk u v)).map old.sym2Map).card :=
      Finset.card_le_card hsub
    _ = (original.erase (Sym2.mk u v)).card := Finset.card_map _
    _ < original.card := Finset.card_erase_lt_of_mem hmem
    _ = beta G := by
      dsimp [original, beta]
      congr!

end Qatlib.Papers.MinorClosed10.MainResults.Source
