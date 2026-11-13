/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MinorClosed10.MainResults.Model.PaperObjects

set_option backward.isDefEq.respectTransparency false

/-!
# Monotonicity of the Internal-Edge Count Under Topological Minors

This module formalizes Lemma 3.2 of Childs and Kothari showing that the number
`β` of internal edges is monotone with respect to topological-minor containment.

## Main statements

* `lemma32`: Lemma 3.2, `ContainsTopologicalMinor H G → beta H ≤ beta G`.

## References

* [Childs and Kothari, 2012][ChildsKothari2012], Section 3, Lemma 3.2, p. 10.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MinorClosed10.MainResults.Source

open Qatlib.Papers.MinorClosed10.MainResults

/- The routes are simplified before selecting their first edges.  Reachability
after deleting a selected edge can then be lifted directly. -/
private structure SubdivisionModel {m n : ℕ}
    (H : SimpleGraph (Fin m)) (G : SimpleGraph (Fin n)) where
  vertex : Fin m ↪ Fin n
  route : ∀ a b, H.Adj a b → G.Walk (vertex a) (vertex b)
  simple : ∀ a b h, (route a b h).IsPath
  avoid : ∀ a b h x, x ∈ WalkInterior (route a b h) → x ∉ Set.range vertex
  separate : ∀ a b hab c d hcd x,
    ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) →
    x ∈ WalkInterior (route a b hab) → x ∈ WalkInterior (route c d hcd) → False

variable {m n : ℕ} {H : SimpleGraph (Fin m)} {G : SimpleGraph (Fin n)}

private theorem SubdivisionModel.not_nil (M : SubdivisionModel H G)
    {a b : Fin m} (hab : H.Adj a b) : ¬ (M.route a b hab).Nil :=
  SimpleGraph.Walk.not_nil_of_ne (M.vertex.injective.ne hab.ne)

private def SubdivisionModel.first (M : SubdivisionModel H G)
    (a b : Fin m) (hab : H.Adj a b) : Fin n := (M.route a b hab).snd

private theorem SubdivisionModel.first_adj (M : SubdivisionModel H G)
    {a b : Fin m} (hab : H.Adj a b) : G.Adj (M.vertex a) (M.first a b hab) :=
  (M.route a b hab).adj_snd (M.not_nil hab)

private theorem SubdivisionModel.first_mem (M : SubdivisionModel H G)
    {a b : Fin m} (hab : H.Adj a b) :
    s(M.vertex a, M.first a b hab) ∈ (M.route a b hab).edges :=
  SimpleGraph.Walk.mk_start_snd_mem_edges (M.not_nil hab)

private theorem SubdivisionModel.branch_support (M : SubdivisionModel H G)
    {a b c : Fin m} (hab : H.Adj a b)
    (hc : M.vertex c ∈ (M.route a b hab).support) : c = a ∨ c = b := by
  by_contra hn
  have hca : c ≠ a := fun h => hn (Or.inl h)
  have hcb : c ≠ b := fun h => hn (Or.inr h)
  exact M.avoid a b hab (M.vertex c)
    ⟨hc, M.vertex.injective.ne hca, M.vertex.injective.ne hcb⟩ ⟨c, rfl⟩

/-- A selected first edge can occur only in routes for the same source edge. -/
private theorem SubdivisionModel.source_of_first (M : SubdivisionModel H G)
    {a b c d : Fin m} (hab : H.Adj a b) (hcd : H.Adj c d)
    (he : s(M.vertex a, M.first a b hab) ∈ (M.route c d hcd).edges) :
    s(a, b) = s(c, d) := by
  have ha := M.branch_support hcd ((M.route c d hcd).fst_mem_support_of_mem_edges he)
  have hx := (M.route a b hab).snd_mem_support_of_mem_edges (M.first_mem hab)
  have hy := (M.route c d hcd).snd_mem_support_of_mem_edges he
  by_cases hxb : M.first a b hab = M.vertex b
  · have hb := M.branch_support hcd (hxb ▸ hy)
    have hne := hab.ne
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact (hne (ha.trans hb.symm)).elim
    · exact Sym2.eq_iff.mpr (Or.inl ⟨ha, hb⟩)
    · exact Sym2.eq_iff.mpr (Or.inr ⟨ha, hb⟩)
    · exact (hne (ha.trans hb.symm)).elim
  · have hi : M.first a b hab ∈ WalkInterior (M.route a b hab) :=
      ⟨hx, (M.first_adj hab).ne.symm, hxb⟩
    have hr := M.avoid a b hab (M.first a b hab) hi
    have hj : M.first a b hab ∈ WalkInterior (M.route c d hcd) :=
      ⟨hy, fun h => hr ⟨c, h.symm⟩, fun h => hr ⟨d, h.symm⟩⟩
    by_contra hn
    exact M.separate a b hab c d hcd _ (fun h => hn (Sym2.eq_iff.mpr h)) hi hj

private theorem SubdivisionModel.degree_le [DecidableRel H.Adj] [DecidableRel G.Adj]
    (M : SubdivisionModel H G) (a : Fin m) :
    H.degree a ≤ G.degree (M.vertex a) := by
  classical
  let f : H.neighborSet a → G.neighborSet (M.vertex a) :=
    fun b => ⟨M.first a b.val b.property, M.first_adj b.property⟩
  rw [← H.card_neighborSet_eq_degree, ← G.card_neighborSet_eq_degree]
  apply Fintype.card_le_of_injective f
  intro b c he
  have hx : M.first a b.val b.property = M.first a c.val c.property :=
    congrArg Subtype.val he
  have hs := M.source_of_first b.property c.property (hx.symm ▸ M.first_mem c.property)
  apply Subtype.ext
  rcases Sym2.eq_iff.mp hs with h | h
  · exact h.2
  · exact h.2.trans h.1

private theorem SubdivisionModel.lift_deleted (M : SubdivisionModel H G)
    {a b : Fin m} (hab : H.Adj a b) {u v : Fin m}
    (huv : (H.deleteEdges {s(a, b)}).Reachable u v) :
    (G.deleteEdges {s(M.vertex a, M.first a b hab)}).Reachable
      (M.vertex u) (M.vertex v) := by
  obtain ⟨p⟩ := huv
  induction p with
  | nil => exact .rfl
  | @cons u x v hux p ih =>
    obtain ⟨hux, hne⟩ := SimpleGraph.deleteEdges_adj.mp hux
    have hn : s(M.vertex a, M.first a b hab) ∉ (M.route u x hux).edges := by
      intro he
      exact hne (Set.mem_singleton_iff.mpr (M.source_of_first hab hux he).symm)
    exact ((M.route u x hux).toDeleteEdge _ hn).reachable.trans ih

private theorem SubdivisionModel.tail_deleted (M : SubdivisionModel H G)
    {a b : Fin m} (hab : H.Adj a b) :
    (G.deleteEdges {s(M.vertex a, M.first a b hab)}).Reachable
      (M.first a b hab) (M.vertex b) := by
  have hs := (M.simple a b hab).isTrail.edges_nodup
  rw [← (M.route a b hab).cons_tail_eq (M.not_nil hab),
    SimpleGraph.Walk.edges_cons, List.nodup_cons] at hs
  exact ((M.route a b hab).tail.toDeleteEdge _ hs.1).reachable

private theorem SubdivisionModel.internal_first (M : SubdivisionModel H G)
    {a b : Fin m} (hi : IsInternalEdge H a b) :
    IsInternalEdge G (M.vertex a) (M.first a b hi.1) := by
  classical
  rcases hi with ⟨hab, hcycle | ⟨⟨u, hu, hdu⟩, ⟨v, hv, hdv⟩⟩⟩
  · refine ⟨M.first_adj hab, Or.inl ?_⟩
    exact (M.lift_deleted hab hcycle).trans (M.tail_deleted hab).symm
  · refine ⟨M.first_adj hab, Or.inr ⟨?_, ?_⟩⟩
    · exact ⟨M.vertex u, M.lift_deleted hab hu, hdu.trans (M.degree_le u)⟩
    · exact ⟨M.vertex v, (M.tail_deleted hab).trans (M.lift_deleted hab hv),
        hdv.trans (M.degree_le v)⟩

/-- Lemma 3.2: `β` is monotone with respect to topological-minor containment. -/
theorem lemma32 {m n : ℕ} (H : SimpleGraph (Fin m)) (G : SimpleGraph (Fin n))
    (h : ContainsTopologicalMinor H G) : beta H ≤ beta G := by
  classical
  obtain ⟨φ, P, havoid, hseparate⟩ := h
  let M : SubdivisionModel H G := {
    vertex := φ
    route := fun a b hab => (P a b hab).toPath.val
    simple := fun a b hab => (P a b hab).toPath.property
    avoid := fun a b hab x hx => havoid a b hab x
      ⟨(P a b hab).support_toPath_subset_support hx.1, hx.2⟩
    separate := fun a b hab c d hcd x hne hx hy => hseparate a b hab c d hcd x hne
      ⟨(P a b hab).support_toPath_subset_support hx.1, hx.2⟩
      ⟨(P c d hcd).support_toPath_subset_support hy.1, hy.2⟩ }
  let S := H.edgeFinset.filter (fun e => ∃ a b, e = s(a, b) ∧ IsInternalEdge H a b)
  let T := G.edgeFinset.filter (fun e => ∃ a b, e = s(a, b) ∧ IsInternalEdge G a b)
  have reps (e : S) : ∃ a b, e.val = s(a, b) ∧ IsInternalEdge H a b :=
    (Finset.mem_filter.mp e.property).2
  choose a b he hi using reps
  let f : S → T := fun e =>
    ⟨s(M.vertex (a e), M.first (a e) (b e) (hi e).1),
      Finset.mem_filter.mpr ⟨SimpleGraph.mem_edgeFinset.mpr (M.first_adj (hi e).1),
        _, _, rfl, M.internal_first (hi e)⟩⟩
  have hc : S.card ≤ T.card := by
    apply Finset.card_le_card_of_injective (f := f)
    intro e₁ e₂ hf
    have hx : s(M.vertex (a e₁), M.first (a e₁) (b e₁) (hi e₁).1) =
        s(M.vertex (a e₂), M.first (a e₂) (b e₂) (hi e₂).1) := congrArg Subtype.val hf
    have hs := M.source_of_first (hi e₁).1 (hi e₂).1 (hx.symm ▸ M.first_mem (hi e₂).1)
    exact Subtype.ext ((he e₁).trans (hs.trans (he e₂).symm))
  have hS : beta H = S.card := by
    unfold beta
    congr 1
    ext e
    simp [S]
  have hT : beta G = T.card := by
    unfold beta
    congr 1
    ext e
    simp [T]
  exact hS.trans_le (hc.trans_eq hT.symm)

end Qatlib.Papers.MinorClosed10.MainResults.Source
