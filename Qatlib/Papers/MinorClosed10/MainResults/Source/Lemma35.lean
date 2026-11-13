/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MinorClosed10.MainResults.Model.PaperObjects
import Qatlib.Papers.MinorClosed10.MainResults.Source.Lemma32
import Qatlib.Papers.MinorClosed10.MainResults.Source.Lemma33
import Qatlib.Papers.MinorClosed10.MainResults.Source.Lemma34

set_option backward.isDefEq.respectTransparency false

/-!
# Existence of a Splittable Edge for Non-FSP Forbidden-Topological-Minor Properties

This module formalizes Lemma 3.5 of Childs and Kothari showing that if a graph
property `P` is described by a finite set of forbidden topological minors and is
not a forbidden subgraph property (`¬ IsFSP P`), then there exists a finite
graph `G ∉ P` with an edge `(u, v)` whose two-path splits all satisfy `P`
(`SplitsInto P G u v`).

## Main statements

* `lemma35`: Lemma 3.5, existence of `(k, G, u, v)` with `¬ P (Fin k) G`,
  `G.Adj u v`, and `SplitsInto P G u v`.

## References

* [Childs and Kothari, 2012][ChildsKothari2012], Section 3, Lemma 3.5, pp. 11--12.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MinorClosed10.MainResults.Source

open Qatlib.Papers.MinorClosed10.MainResults

/- Simple path models allow composition and controlled changes of branch vertices. -/
private structure l35Model {V W : Type} (H : SimpleGraph V) (G : SimpleGraph W) where
  vertex : V ↪ W
  route : ∀ a b, H.Adj a b → G.Walk (vertex a) (vertex b)
  simple : ∀ a b h, (route a b h).IsPath
  avoid : ∀ a b h x, x ∈ WalkInterior (route a b h) → x ∉ Set.range vertex
  separate : ∀ a b hab c d hcd x,
    ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) →
    x ∈ WalkInterior (route a b hab) → x ∈ WalkInterior (route c d hcd) → False

private theorem l35SimpleModel {V W : Type} {H : SimpleGraph V} {G : SimpleGraph W}
    (h : ContainsTopologicalMinor H G) : Nonempty (l35Model H G) := by
  classical
  obtain ⟨φ, p, ha, hs⟩ := h
  exact ⟨{
    vertex := φ
    route := fun a b hab => (p a b hab).toPath.val
    simple := fun a b hab => (p a b hab).toPath.property
    avoid := fun a b hab x hx => ha a b hab x
      ⟨(p a b hab).support_toPath_subset_support hx.1, hx.2⟩
    separate := fun a b hab c d hcd x hne hx hy => hs a b hab c d hcd x hne
      ⟨(p a b hab).support_toPath_subset_support hx.1, hx.2⟩
      ⟨(p c d hcd).support_toPath_subset_support hy.1, hy.2⟩ }⟩

private theorem l35Model.contains {V W : Type} {H : SimpleGraph V} {G : SimpleGraph W}
    (M : l35Model H G) : ContainsTopologicalMinor H G :=
  ⟨M.vertex, M.route, M.avoid, M.separate⟩

private theorem l35SubgraphTopological {V W : Type} {H : SimpleGraph V}
    {G : SimpleGraph W} (h : ContainsSubgraph H G) : ContainsTopologicalMinor H G := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ, fun _ _ hab => .cons (hφ hab) .nil, ?_, ?_⟩
  · intro a b hab x hx
    simp [WalkInterior] at hx
    exact (hx.1.elim hx.2.1 hx.2.2).elim
  · intro a b hab c d hcd x _ hx _
    simp [WalkInterior] at hx
    exact hx.1.elim hx.2.1 hx.2.2

private theorem l35Model.branch_support {V W : Type} {H : SimpleGraph V}
    {G : SimpleGraph W} (M : l35Model H G) {a b c : V} (hab : H.Adj a b)
    (hc : M.vertex c ∈ (M.route a b hab).support) : c = a ∨ c = b := by
  by_contra hn
  exact M.avoid a b hab (M.vertex c)
    ⟨hc, M.vertex.injective.ne (fun h => hn (.inl h)),
      M.vertex.injective.ne (fun h => hn (.inr h))⟩ ⟨c, rfl⟩

private theorem l35Model.shared {V W : Type} {H : SimpleGraph V}
    {G : SimpleGraph W} (M : l35Model H G) {a b c d : V}
    (hab : H.Adj a b) (hcd : H.Adj c d)
    (hne : ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c))) {x : W}
    (hx : x ∈ (M.route a b hab).support) (hy : x ∈ (M.route c d hcd).support) :
    ∃ z, x = M.vertex z ∧ (z = a ∨ z = b) ∧ (z = c ∨ z = d) := by
  classical
  by_cases hr : x ∈ Set.range M.vertex
  · obtain ⟨z, rfl⟩ := hr
    exact ⟨z, rfl, M.branch_support hab hx, M.branch_support hcd hy⟩
  · exact (M.separate a b hab c d hcd x hne
      ⟨hx, fun h => hr ⟨a, h.symm⟩, fun h => hr ⟨b, h.symm⟩⟩
      ⟨hy, fun h => hr ⟨c, h.symm⟩, fun h => hr ⟨d, h.symm⟩⟩).elim

private def l35Expand {V W : Type} {H : SimpleGraph V} {G : SimpleGraph W}
    (M : l35Model H G) {a b : V} : H.Walk a b → G.Walk (M.vertex a) (M.vertex b)
  | .nil => .nil
  | .cons hab p => (M.route _ _ hab).append (l35Expand M p)

private theorem l35ExpandSupport {V W : Type} {H : SimpleGraph V} {G : SimpleGraph W}
    (M : l35Model H G) {a b : V} (p : H.Walk a b) {x : W}
    (hx : x ∈ (l35Expand M p).support) :
    (∃ c ∈ p.support, x = M.vertex c) ∨
      ∃ c d, ∃ h : H.Adj c d, s(c, d) ∈ p.edges ∧ x ∈ WalkInterior (M.route c d h) := by
  induction p with
  | @nil a =>
    exact .inl ⟨a, by simp, by simpa [l35Expand] using hx⟩
  | @cons a b c hab p ih =>
    rw [l35Expand, SimpleGraph.Walk.mem_support_append_iff] at hx
    rcases hx with hx | hx
    · by_cases ha : x = M.vertex a
      · exact .inl ⟨a, by simp, ha⟩
      by_cases hb : x = M.vertex b
      · exact .inl ⟨b, by simp, hb⟩
      exact .inr ⟨a, b, hab, by simp, hx, ha, hb⟩
    · rcases ih hx with ⟨d, hd, hxd⟩ | ⟨d, e, hde, he, hx⟩
      · exact .inl ⟨d, by simp [hd], hxd⟩
      · exact .inr ⟨d, e, hde, by simp [he], hx⟩

private theorem l35ExpandRange {V W : Type} {H : SimpleGraph V} {G : SimpleGraph W}
    (M : l35Model H G) {a b c : V} (p : H.Walk a b)
    (hc : M.vertex c ∈ (l35Expand M p).support) : c ∈ p.support := by
  rcases l35ExpandSupport M p hc with ⟨d, hd, hcd⟩ | ⟨d, e, hde, _, hx⟩
  · exact (M.vertex.injective hcd).symm ▸ hd
  · exact (M.avoid d e hde _ hx ⟨c, rfl⟩).elim

private theorem l35TopologicalTrans {U V W : Type} {H : SimpleGraph U}
    {K : SimpleGraph V} {G : SimpleGraph W}
    (h₁ : ContainsTopologicalMinor H K) (h₂ : ContainsTopologicalMinor K G) :
    ContainsTopologicalMinor H G := by
  classical
  obtain ⟨M⟩ := l35SimpleModel h₁
  obtain ⟨N⟩ := l35SimpleModel h₂
  refine ⟨M.vertex.trans N.vertex, fun a b hab => l35Expand N (M.route a b hab), ?_, ?_⟩
  · intro a b hab x hx ⟨c, hc⟩
    have hmem := l35ExpandRange N (M.route a b hab) (hc ▸ hx.1)
    apply M.avoid a b hab (M.vertex c) ⟨hmem, ?_, ?_⟩ ⟨c, rfl⟩
    · intro heq
      exact hx.2.1 (hc.symm.trans (congrArg N.vertex heq))
    · intro heq
      exact hx.2.2 (hc.symm.trans (congrArg N.vertex heq))
  · intro a b hab c d hcd x hne hx hy
    have hcommon : ∀ z, z ∈ (M.route a b hab).support →
        z ∈ (M.route c d hcd).support →
        ∃ t, z = M.vertex t ∧ (t = a ∨ t = b) ∧ (t = c ∨ t = d) :=
      fun z hz hz' => M.shared hab hcd hne hz hz'
    rcases l35ExpandSupport N (M.route a b hab) hx.1 with
      ⟨z, hz, hxz⟩ | ⟨u, v, huv, he, hxu⟩
    · obtain ⟨t, ht, hta, _⟩ := hcommon z hz
        (l35ExpandRange N (M.route c d hcd) (hxz ▸ hy.1))
      rcases hta with rfl | rfl
      · exact hx.2.1 (hxz.trans (congrArg N.vertex ht))
      · exact hx.2.2 (hxz.trans (congrArg N.vertex ht))
    · rcases l35ExpandSupport N (M.route c d hcd) hy.1 with
        ⟨z, _, hxz⟩ | ⟨u', v', huv', he', hxv⟩
      · exact N.avoid u v huv x hxu ⟨z, hxz.symm⟩
      · by_cases hs : (u = u' ∧ v = v') ∨ (u = v' ∧ v = u')
        · have hu := (M.route a b hab).fst_mem_support_of_mem_edges he
          have hv := (M.route a b hab).snd_mem_support_of_mem_edges he
          have hu' := (M.route c d hcd).fst_mem_support_of_mem_edges he'
          have hv' := (M.route c d hcd).snd_mem_support_of_mem_edges he'
          have hun : u ≠ v := huv.ne
          rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          all_goals
            obtain ⟨t, ht, hta, htc⟩ := hcommon _ hu (by assumption)
            obtain ⟨r, hr, hra, hrc⟩ := hcommon _ hv (by assumption)
            have htr : t ≠ r := fun h => hun (ht.trans ((congrArg M.vertex h).trans hr.symm))
            rcases hta with rfl | rfl <;> rcases hra with rfl | rfl <;>
              rcases htc with htc | htc <;> rcases hrc with hrc | hrc
            all_goals first
              | exact htr rfl
              | exact hab.ne (htc.trans hrc.symm)
              | exact hab.ne (hrc.trans htc.symm)
              | exact hne (.inl ⟨htc, hrc⟩)
              | exact hne (.inr ⟨htc, hrc⟩)
              | exact hne (.inl ⟨hrc, htc⟩)
              | exact hne (.inr ⟨hrc, htc⟩)
        · exact N.separate u v huv u' v' huv' x hs hxu hxv

private theorem l35PathInterior {W : Type} {G : SimpleGraph W} {u v : W}
    (p : G.Walk u v) (hp : p.IsPath) {i : ℕ} (hi : 0 < i) (hil : i < p.length) :
    p.getVert i ∈ WalkInterior p := by
  refine ⟨p.getVert_mem_support i, ?_, ?_⟩
  · intro h
    have he := hp.getVert_injOn (by simpa using hil.le) (by simp)
      (h.trans (p.getVert_zero).symm)
    omega
  · intro h
    have he := hp.getVert_injOn (by simpa using hil.le) (by simp)
      (h.trans (p.getVert_length).symm)
    omega

private theorem l35OneEdgeInterior {W : Type} {G : SimpleGraph W} {u v x : W}
    (h : G.Adj u v) (hx : x ∈ WalkInterior (SimpleGraph.Walk.cons h .nil)) : False := by
  simp [WalkInterior] at hx
  exact hx.1.elim hx.2.1 hx.2.2

private theorem l35SplitOldAdj {k n₁ n₂ : ℕ} (H : SimpleGraph (Fin k))
    (u v a b : Fin k) :
    (twoPathSplitSum H u v n₁ n₂).Adj (.inl (.inl a)) (.inl (.inl b)) ↔
      H.Adj a b ∧ s(a, b) ≠ s(u, v) := by
  have hab : H.Adj a b → a ≠ b := SimpleGraph.Adj.ne
  have hba : H.Adj b a ↔ H.Adj a b := H.adj_comm b a
  simp only [twoPathSplitSum, SimpleGraph.fromRel_adj, ne_eq, Sum.inl.injEq, Sym2.eq_iff]
  tauto

private def l35SplitPlace {k n₁ n₂ : ℕ} {W : Type}
    {H : SimpleGraph (Fin k)} {G : SimpleGraph W} (M : l35Model H G)
    {u v : Fin k} (huv : H.Adj u v) : ((Fin k ⊕ Fin n₁) ⊕ Fin n₂) → W
  | .inl (.inl a) => M.vertex a
  | .inl (.inr i) => (M.route u v huv).getVert (i.val + 1)
  | .inr j => (M.route u v huv).reverse.getVert (j.val + 1)

private theorem l35SplitPlace_left {k n₁ n₂ : ℕ} {W : Type}
    {H : SimpleGraph (Fin k)} {G : SimpleGraph W} (M : l35Model H G)
    {u v : Fin k} (huv : H.Adj u v)
    (hlen : n₁ + n₂ + 1 < (M.route u v huv).length) (i : Fin n₁) :
    l35SplitPlace (n₂ := n₂) M huv (.inl (.inr i)) ∈ WalkInterior (M.route u v huv) :=
  l35PathInterior _ (M.simple u v huv) (by omega) (by omega)

private theorem l35SplitPlace_right {k n₁ n₂ : ℕ} {W : Type}
    {H : SimpleGraph (Fin k)} {G : SimpleGraph W} (M : l35Model H G)
    {u v : Fin k} (huv : H.Adj u v)
    (hlen : n₁ + n₂ + 1 < (M.route u v huv).length) (j : Fin n₂) :
    l35SplitPlace (n₁ := n₁) M huv (.inr j) ∈ WalkInterior (M.route u v huv) := by
  have h := l35PathInterior (M.route u v huv).reverse (M.simple u v huv).reverse
    (i := j.val + 1) (by omega) (by simp only [SimpleGraph.Walk.length_reverse]; omega)
  exact ⟨by simpa only [l35SplitPlace, SimpleGraph.Walk.support_reverse, List.mem_reverse] using h.1,
    h.2.2, h.2.1⟩

private theorem l35LongSplit {k : ℕ} {W : Type} {H : SimpleGraph (Fin k)}
    {G : SimpleGraph W} (M : l35Model H G) {u v : Fin k} (huv : H.Adj u v)
    (n₁ n₂ : ℕ) (hlen : n₁ + n₂ + 1 < (M.route u v huv).length) :
    ContainsTopologicalMinor (twoPathSplitSum H u v n₁ n₂) G := by
  classical
  let p := M.route u v huv
  have hinj : ∀ i j, i ≤ p.length → j ≤ p.length → p.getVert i = p.getVert j → i = j :=
    fun i j hi hj h => (M.simple u v huv).getVert_injOn hi hj h
  let f : ((Fin k ⊕ Fin n₁) ⊕ Fin n₂) ↪ W := {
    toFun := l35SplitPlace M huv
    inj' := by
      intro a b he
      rcases a with ((a | a) | a) <;> rcases b with ((b | b) | b)
      · exact congrArg (fun x => Sum.inl (Sum.inl x)) (M.vertex.injective he)
      · exact (M.avoid u v huv _ (l35SplitPlace_left M huv hlen b) ⟨a, he⟩).elim
      · exact (M.avoid u v huv _ (l35SplitPlace_right M huv hlen b) ⟨a, he⟩).elim
      · exact (M.avoid u v huv _ (l35SplitPlace_left M huv hlen a) ⟨b, he.symm⟩).elim
      · have he' := hinj (a.val + 1) (b.val + 1) (by dsimp [p]; omega)
          (by dsimp [p]; omega) he
        exact congrArg (fun x => Sum.inl (Sum.inr x)) (Fin.ext (by omega))
      · have he' : p.getVert (a.val + 1) = p.getVert (p.length - (b.val + 1)) := by
          simpa only [l35SplitPlace, p, SimpleGraph.Walk.getVert_reverse] using he
        have hi := hinj _ _ (by dsimp [p]; omega) (Nat.sub_le ..) he'
        dsimp [p] at hi
        omega
      · exact (M.avoid u v huv _ (l35SplitPlace_right M huv hlen a) ⟨b, he.symm⟩).elim
      · have he' : p.getVert (p.length - (a.val + 1)) = p.getVert (b.val + 1) := by
          simpa only [l35SplitPlace, p, SimpleGraph.Walk.getVert_reverse] using he
        have hi := hinj _ _ (Nat.sub_le ..) (by dsimp [p]; omega) he'
        dsimp [p] at hi
        omega
      · have he' : p.getVert (p.length - (a.val + 1)) =
            p.getVert (p.length - (b.val + 1)) := by
          simpa only [l35SplitPlace, p, SimpleGraph.Walk.getVert_reverse] using he
        have hi := hinj _ _ (Nat.sub_le ..) (Nat.sub_le ..) he'
        exact congrArg Sum.inr (Fin.ext (by dsimp [p] at hi; omega)) }
  have hnew : ∀ a b, (twoPathSplitSum H u v n₁ n₂).Adj a b →
      ¬ (∃ x y : Fin k, a = .inl (.inl x) ∧ b = .inl (.inl y)) →
      G.Adj (f a) (f b) := by
    intro a b hab hn
    rcases a with ((a | a) | a) <;> rcases b with ((b | b) | b)
    · exact (hn ⟨a, b, rfl, rfl⟩).elim
    · have hs : a = u ∧ b.val = 0 := by
        simpa [twoPathSplitSum, SimpleGraph.fromRel_adj] using hab
      obtain ⟨rfl, hb⟩ := hs
      simpa only [f, Function.Embedding.coeFn_mk, l35SplitPlace, hb, Nat.zero_add,
        p, SimpleGraph.Walk.getVert_zero] using
        p.adj_getVert_succ (i := 0) (by dsimp [p]; omega)
    · have hs : a = v ∧ b.val = 0 := by
        simpa [twoPathSplitSum, SimpleGraph.fromRel_adj] using hab
      obtain ⟨rfl, hb⟩ := hs
      simpa only [f, Function.Embedding.coeFn_mk, l35SplitPlace, hb, Nat.zero_add,
        p, SimpleGraph.Walk.getVert_zero] using
        p.reverse.adj_getVert_succ (i := 0) (by simp only [SimpleGraph.Walk.length_reverse]; dsimp [p]; omega)
    · have hs : b = u ∧ a.val = 0 := by
        simpa [twoPathSplitSum, SimpleGraph.fromRel_adj] using hab
      obtain ⟨rfl, ha⟩ := hs
      apply SimpleGraph.Adj.symm
      simpa only [f, Function.Embedding.coeFn_mk, l35SplitPlace, ha, Nat.zero_add,
        p, SimpleGraph.Walk.getVert_zero] using
        p.adj_getVert_succ (i := 0) (by dsimp [p]; omega)
    · have hs : a ≠ b ∧ (a.val + 1 = b.val ∨ b.val + 1 = a.val) := by
        simpa [twoPathSplitSum, SimpleGraph.fromRel_adj] using hab
      rcases hs.2 with hs | hs
      · simpa only [f, Function.Embedding.coeFn_mk, l35SplitPlace, p, ← hs] using
          p.adj_getVert_succ (i := a.val + 1) (by dsimp [p]; omega)
      · apply SimpleGraph.Adj.symm
        simpa only [f, Function.Embedding.coeFn_mk, l35SplitPlace, p, ← hs] using
          p.adj_getVert_succ (i := b.val + 1) (by dsimp [p]; omega)
    · simp [twoPathSplitSum, SimpleGraph.fromRel_adj] at hab
    · have hs : b = v ∧ a.val = 0 := by
        simpa [twoPathSplitSum, SimpleGraph.fromRel_adj] using hab
      obtain ⟨rfl, ha⟩ := hs
      apply SimpleGraph.Adj.symm
      simpa only [f, Function.Embedding.coeFn_mk, l35SplitPlace, ha, Nat.zero_add,
        p, SimpleGraph.Walk.getVert_zero] using
        p.reverse.adj_getVert_succ (i := 0)
          (by simp only [SimpleGraph.Walk.length_reverse]; dsimp [p]; omega)
    · simp [twoPathSplitSum, SimpleGraph.fromRel_adj] at hab
    · have hs : a ≠ b ∧ (a.val + 1 = b.val ∨ b.val + 1 = a.val) := by
        simpa [twoPathSplitSum, SimpleGraph.fromRel_adj] using hab
      rcases hs.2 with hs | hs
      · simpa only [f, Function.Embedding.coeFn_mk, l35SplitPlace, p, ← hs] using
          p.reverse.adj_getVert_succ (i := a.val + 1)
            (by simp only [SimpleGraph.Walk.length_reverse]; dsimp [p]; omega)
      · apply SimpleGraph.Adj.symm
        simpa only [f, Function.Embedding.coeFn_mk, l35SplitPlace, p, ← hs] using
          p.reverse.adj_getVert_succ (i := b.val + 1)
            (by simp only [SimpleGraph.Walk.length_reverse]; dsimp [p]; omega)
  let route : ∀ a b, (twoPathSplitSum H u v n₁ n₂).Adj a b → G.Walk (f a) (f b) := by
    intro a b hab
    rcases a with ((a | a) | a) <;> rcases b with ((b | b) | b)
    · exact M.route a b ((l35SplitOldAdj H u v a b).mp hab).1
    all_goals exact .cons (hnew _ _ hab (by simp)) .nil
  refine ⟨f, route, ?_, ?_⟩
  · intro a b hab x hx ⟨c, hc⟩
    rcases a with ((a | a) | a) <;> rcases b with ((b | b) | b)
    · have hold := (l35SplitOldAdj H u v a b).mp hab
      change x ∈ WalkInterior (M.route a b hold.1) at hx
      rcases c with ((c | c) | c)
      · exact M.avoid a b hold.1 x hx ⟨c, hc⟩
      · exact M.separate a b hold.1 u v huv x
          (fun h => hold.2 (Sym2.eq_iff.mpr h)) hx (hc ▸ l35SplitPlace_left M huv hlen c)
      · exact M.separate a b hold.1 u v huv x
          (fun h => hold.2 (Sym2.eq_iff.mpr h)) hx (hc ▸ l35SplitPlace_right M huv hlen c)
    all_goals exact l35OneEdgeInterior _ hx
  · intro a b hab c d hcd x hne hx hy
    rcases a with ((a | a) | a) <;> rcases b with ((b | b) | b)
    · rcases c with ((c | c) | c) <;> rcases d with ((d | d) | d)
      · apply M.separate a b ((l35SplitOldAdj H u v a b).mp hab).1
          c d ((l35SplitOldAdj H u v c d).mp hcd).1 x (by simpa using hne) hx hy
      all_goals exact l35OneEdgeInterior _ hy
    all_goals exact l35OneEdgeInterior _ hx

/- A dangling arm can be placed along the beginning of its expanded path. -/

open scoped Classical

private theorem l35ExpandLength {V W : Type} {H : SimpleGraph V} {G : SimpleGraph W}
    (M : l35Model H G) {a b : V} (p : H.Walk a b) :
    p.length ≤ (l35Expand M p).length := by
  induction p with
  | nil => exact Nat.le_refl 0
  | @cons a b c hab p ih =>
    have hpos : 0 < (M.route a b hab).length := Nat.pos_of_ne_zero fun h =>
      hab.ne (M.vertex.injective (SimpleGraph.Walk.eq_of_length_eq_zero h))
    simp only [l35Expand, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons]
    omega

private theorem l35ExpandMeet {V W : Type} {H : SimpleGraph V} {G : SimpleGraph W}
    (M : l35Model H G) {a b c d : V} (p : H.Walk a b) (q : H.Walk c d) (r : V)
    (hcommon : ∀ z, z ∈ p.support → z ∈ q.support → z = r)
    {x : W} (hp : x ∈ (l35Expand M p).support)
    (hq : x ∈ (l35Expand M q).support) : x = M.vertex r := by
  rcases l35ExpandSupport M p hp with ⟨u, hu, rfl⟩ | ⟨u, v, huv, he, hx⟩
  · exact congrArg M.vertex (hcommon u hu (l35ExpandRange M q hq))
  rcases l35ExpandSupport M q hq with ⟨u', _, heq⟩ | ⟨u', v', huv', he', hx'⟩
  · exact (M.avoid u v huv x hx ⟨u', heq.symm⟩).elim
  by_cases hsame : (u = u' ∧ v = v') ∨ (u = v' ∧ v = u')
  · have hu := p.fst_mem_support_of_mem_edges he
    have hv := p.snd_mem_support_of_mem_edges he
    have hu' := q.fst_mem_support_of_mem_edges he'
    have hv' := q.snd_mem_support_of_mem_edges he'
    rcases hsame with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (huv.ne ((hcommon _ hu hu').trans (hcommon _ hv hv').symm)).elim
    · exact (huv.ne ((hcommon _ hu hv').trans (hcommon _ hv hu').symm)).elim
  · exact (M.separate u v huv u' v' huv' x hsame hx hx').elim

private theorem l35PathEndNotDropLast {V : Type} {H : SimpleGraph V} {a b : V}
    (p : H.Walk a b) (hp : p.IsPath) : b ∉ p.support.dropLast := by
  intro hb
  have hnodup := hp.support_nodup
  rw [← p.dropLast_support_concat] at hnodup
  exact List.disjoint_of_nodup_append hnodup hb (by simp)

private theorem l35ExpandPath {V W : Type} {H : SimpleGraph V} {G : SimpleGraph W}
    (M : l35Model H G) {a b : V} (p : H.Walk a b) (hp : p.IsPath) :
    (l35Expand M p).IsPath := by
  induction p with
  | nil => exact .nil
  | @cons a b c hab p ih =>
    have hp' := (SimpleGraph.Walk.cons_isPath_iff hab p).mp hp
    rw [l35Expand, SimpleGraph.Walk.isPath_append']
    refine ⟨(M.simple a b hab).dropLast, ih hp'.1, ?_⟩
    intro x hx hy
    have hx' := List.mem_of_mem_dropLast hx
    have hmeet : x = M.vertex b := by
      apply l35ExpandMeet M (.cons hab .nil) p b
      · intro z hz hz'
        simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
          List.mem_cons, List.not_mem_nil, or_false] at hz
        exact hz.resolve_left (fun h => hp'.2 (h ▸ hz'))
      · simpa [l35Expand] using hx'
      · exact hy
    exact l35PathEndNotDropLast (M.route a b hab) (M.simple a b hab) (hmeet ▸ hx)

private theorem l35SmallDegreeNeighbors {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) {a b c d : V} (hdeg : H.degree a ≤ 2)
    (hab : H.Adj a b) (hac : H.Adj a c) (had : H.Adj a d) (hbc : b ≠ c) :
    d = b ∨ d = c := by
  classical
  by_contra hn
  have hdb : d ≠ b := fun h => hn (.inl h)
  have hdc : d ≠ c := fun h => hn (.inr h)
  have hsub : ({b, c, d} : Finset V) ⊆ H.neighborFinset a := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> simp_all
  have hcard := Finset.card_le_card hsub
  have hthree : ({b, c, d} : Finset V).card = 3 := by
    simp [hbc, Ne.symm hdb, Ne.symm hdc]
  rw [hthree, SimpleGraph.card_neighborFinset_eq_degree] at hcard
  omega

private theorem l35MaximalArm {V : Type} [Fintype V]
    (H : SimpleGraph V) {r u : V} (hru : H.Adj r u) :
    ∃ t, ∃ q : H.Walk r t, q.IsPath ∧ q.snd = u ∧
      ∀ t', ∀ q' : H.Walk r t', q'.IsPath → q'.snd = u → q'.length ≤ q.length := by
  classical
  let S : Finset ℕ := (Finset.range (Fintype.card V)).filter
    (fun n => ∃ t, ∃ q : H.Walk r t, q.IsPath ∧ q.snd = u ∧ q.length = n)
  have hone : 1 ∈ S := by
    refine Finset.mem_filter.mpr ⟨?_, u, hru.toWalk, hru.isPath_toWalk, ?_, ?_⟩
    · exact Finset.mem_range.mpr (by simpa using hru.isPath_toWalk.length_lt)
    · rfl
    · rfl
  have hn : S.Nonempty := ⟨1, hone⟩
  obtain ⟨t, q, hq, hsnd, hlen⟩ := (Finset.mem_filter.mp (S.max'_mem hn)).2
  refine ⟨t, q, hq, hsnd, ?_⟩
  intro t' q' hq' hsnd'
  rw [hlen]
  exact S.le_max' _ (Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr hq'.length_lt, t', q', hq', hsnd', rfl⟩)

private theorem l35ArmTailReach {V : Type} [DecidableEq V] {H : SimpleGraph V}
    {r u t x : V} (p : H.Walk r t) (hp : p.IsPath) (hs : p.snd = u)
    (hr : r ≠ u) (hx : x ∈ p.support) (hxr : x ≠ r) :
    (H.deleteEdges {s(r, u)}).Reachable u x := by
  have hn : ¬p.Nil := by
    intro h
    cases h
    exact hr hs
  have hedge : s(r, u) ∉ p.tail.edges := by
    have hsimp := hp.isTrail.edges_nodup
    rw [← p.cons_tail_eq hn, SimpleGraph.Walk.edges_cons, List.nodup_cons] at hsimp
    simpa only [hs] using hsimp.1
  have hxt : x ∈ p.tail.support := by
    rw [← p.cons_support_tail hn] at hx
    exact (List.mem_cons.mp hx).resolve_left hxr
  have hreach := ((p.tail.toDeleteEdge _ hedge).takeUntil x
    (by simpa only [SimpleGraph.Walk.toDeleteEdge, SimpleGraph.Walk.toDeleteEdges,
      SimpleGraph.Walk.support_transfer] using hxt)).reachable
  simpa only [hs] using hreach

private theorem l35ArmInteriorEdge {V : Type} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {r t y : V} (p : H.Walk r t) (hp : p.IsPath)
    (hdeg : ∀ x ∈ p.support, x ≠ r → H.degree x ≤ 2)
    {i : ℕ} (hi : 0 < i) (hil : i < p.length) (hy : H.Adj (p.getVert i) y) :
    s(p.getVert i, y) ∈ p.edges := by
  have hip : i - 1 < p.length := by omega
  have hprev : H.Adj (p.getVert i) (p.getVert (i - 1)) := by
    have h := (p.adj_getVert_succ hip).symm
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using h
  have hnext := p.adj_getVert_succ hil
  have hne : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
    intro heq
    have := hp.getVert_injOn (by omega : i - 1 ≤ p.length)
      (by omega : i + 1 ≤ p.length) heq
    omega
  have hroot : p.getVert i ≠ r := by
    intro heq
    have := hp.getVert_injOn (by omega : i ≤ p.length) (Nat.zero_le _)
      (heq.trans p.getVert_zero.symm)
    omega
  rcases l35SmallDegreeNeighbors H
    (hdeg _ (p.getVert_mem_support i) hroot) hprev hnext hy hne with h | h
  · apply p.mk_mem_edges_iff_exists.mpr
    exact ⟨i - 1, hip, Sym2.eq_iff.mpr (.inr
      ⟨h.symm, by rw [Nat.sub_add_cancel (by omega : 1 ≤ i)]⟩)⟩
  · apply p.mk_mem_edges_iff_exists.mpr
    exact ⟨i, hil, by rw [h]⟩

private theorem l35ArmClosed {V : Type} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {r u t : V} (hru : H.Adj r u)
    (hbridge : ¬ (H.deleteEdges {s(r, u)}).Reachable r u)
    (hlow : ∀ x, (H.deleteEdges {s(r, u)}).Reachable u x → H.degree x ≤ 2)
    (p : H.Walk r t) (hp : p.IsPath) (hs : p.snd = u)
    (hmax : ∀ t', ∀ q : H.Walk r t', q.IsPath → q.snd = u → q.length ≤ p.length) :
    ∀ x ∈ p.support, x ≠ r → ∀ y, H.Adj x y → s(x, y) ∈ p.edges := by
  have hdeg : ∀ x ∈ p.support, x ≠ r → H.degree x ≤ 2 :=
    fun x hx hxr => hlow x (l35ArmTailReach p hp hs hru.ne hx hxr)
  have hrootEnd : t ≠ r := by
    intro heq
    subst t
    have hnil := (SimpleGraph.Walk.isPath_iff_nil.mp hp)
    cases hnil
    exact hru.ne hs
  have hfinish : ∀ y, H.Adj t y → y ∈ p.support := by
    intro y hty
    by_contra hy
    have hq := hp.concat hy hty
    have hsnd : (p.concat hty).snd = u := by
      cases p with
      | nil => exact (hrootEnd rfl).elim
      | cons => simpa only [SimpleGraph.Walk.concat_cons, SimpleGraph.Walk.snd_cons] using hs
    have hlen := hmax y (p.concat hty) hq hsnd
    simp only [SimpleGraph.Walk.length_concat] at hlen
    omega
  intro x hx hxr y hxy
  obtain ⟨i, hix, hil⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
  have hi : 0 < i := by
    by_contra hn
    have hiz : i = 0 := by omega
    exact hxr (hix.symm.trans (by simp only [hiz, SimpleGraph.Walk.getVert_zero]))
  by_cases hilt : i < p.length
  · exact hix ▸ l35ArmInteriorEdge p hp hdeg hi hilt (hix.symm ▸ hxy)
  have hie : i = p.length := by omega
  have hxt : x = t := by simpa only [hie, SimpleGraph.Walk.getVert_length] using hix.symm
  rw [hxt] at hxy ⊢
  have hyr := hfinish y hxy
  obtain ⟨j, hjy, hjl⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hyr
  by_cases hj : 0 < j
  · have hjlt : j < p.length := by
      by_contra hn
      have hje : j = p.length := by omega
      exact hxy.ne (by simpa only [hje, SimpleGraph.Walk.getVert_length] using hjy)
    have he := l35ArmInteriorEdge p hp hdeg hj hjlt (hjy.symm ▸ hxy.symm)
    simpa only [hjy, Sym2.eq_swap] using he
  · have hjz : j = 0 := by omega
    have hyr : y = r := by simpa only [hjz, SimpleGraph.Walk.getVert_zero] using hjy.symm
    rw [hyr] at hxy ⊢
    by_cases htu : t = u
    · have he : s(r, u) ∈ p.edges := by
        simpa only [hs] using p.mk_start_snd_mem_edges
          (SimpleGraph.Walk.not_nil_of_ne hrootEnd.symm)
      simpa only [htu, Sym2.eq_swap] using he
    · have he : (H.deleteEdges {s(r, u)}).Adj t r := by
        refine SimpleGraph.deleteEdges_adj.mpr ⟨hxy, ?_⟩
        simp only [Set.mem_singleton_iff, Sym2.eq_iff]
        rintro (⟨htr, _⟩ | ⟨htu', _⟩)
        · exact hrootEnd htr
        · exact htu htu'
      exact (hbridge (he.reachable.symm.trans
        (l35ArmTailReach p hp hs hru.ne p.end_mem_support hrootEnd).symm)).elim

private def l35Slide {V W : Type} [DecidableEq V]
    {H : SimpleGraph V} {G : SimpleGraph W} (M : l35Model H G)
    {r t : V} (p : H.Walk r t) (x : V) : W :=
  if x ∈ p.support then (l35Expand M p).getVert (p.support.idxOf x) else M.vertex x

private theorem l35SlideOff {V W : Type} [DecidableEq V]
    {H : SimpleGraph V} {G : SimpleGraph W} (M : l35Model H G)
    {r t x : V} (p : H.Walk r t) (hx : x ∉ p.support) :
    l35Slide M p x = M.vertex x := by
  simp only [l35Slide, hx, ite_false]

private theorem l35SlideGetVert {V W : Type} [DecidableEq V]
    {H : SimpleGraph V} {G : SimpleGraph W} (M : l35Model H G)
    {r t : V} (p : H.Walk r t) (hp : p.IsPath) {i : ℕ} (hi : i ≤ p.length) :
    l35Slide M p (p.getVert i) = (l35Expand M p).getVert i := by
  have hmem := p.getVert_mem_support i
  have hidx : p.support.idxOf (p.getVert i) ≤ p.length := by
    have := List.idxOf_lt_length_of_mem hmem
    rw [SimpleGraph.Walk.length_support] at this
    omega
  have heq : p.support.idxOf (p.getVert i) = i :=
    hp.getVert_injOn hidx hi (p.getVert_support_idxOf hmem)
  simp only [l35Slide, hmem, ite_true, heq]

private theorem l35SlideRoot {V W : Type} [DecidableEq V]
    {H : SimpleGraph V} {G : SimpleGraph W} (M : l35Model H G)
    {r t : V} (p : H.Walk r t) (hp : p.IsPath) : l35Slide M p r = M.vertex r := by
  simpa only [SimpleGraph.Walk.getVert_zero] using
    l35SlideGetVert M p hp (Nat.zero_le p.length)

private theorem l35SlideSupport {V W : Type} [DecidableEq V]
    {H : SimpleGraph V} {G : SimpleGraph W} (M : l35Model H G)
    {r t x : V} (p : H.Walk r t) (hx : x ∈ p.support) :
    l35Slide M p x ∈ (l35Expand M p).support := by
  simpa only [l35Slide, hx, ite_true] using
    (l35Expand M p).getVert_mem_support (p.support.idxOf x)

private theorem l35SlideInjective {V W : Type} [DecidableEq V]
    {H : SimpleGraph V} {G : SimpleGraph W} (M : l35Model H G)
    {r t : V} (p : H.Walk r t) (hp : p.IsPath) :
    Function.Injective (l35Slide M p) := by
  intro x y hxy
  by_cases hx : x ∈ p.support
  · by_cases hy : y ∈ p.support
    · have hxi : p.support.idxOf x ≤ p.length := by
        have := List.idxOf_lt_length_of_mem hx
        rw [SimpleGraph.Walk.length_support] at this
        omega
      have hyi : p.support.idxOf y ≤ p.length := by
        have := List.idxOf_lt_length_of_mem hy
        rw [SimpleGraph.Walk.length_support] at this
        omega
      have hi := (l35ExpandPath M p hp).getVert_injOn
        (hxi.trans (l35ExpandLength M p)) (hyi.trans (l35ExpandLength M p))
        (by simpa only [l35Slide, hx, hy, ite_true] using hxy)
      exact (p.getVert_support_idxOf hx).symm.trans
        ((congrArg p.getVert hi).trans (p.getVert_support_idxOf hy))
    · have hr : M.vertex y ∈ (l35Expand M p).support := by
        rw [← l35SlideOff M p hy, ← hxy]
        exact l35SlideSupport M p hx
      exact (hy (l35ExpandRange M p hr)).elim
  · by_cases hy : y ∈ p.support
    · have hr : M.vertex x ∈ (l35Expand M p).support := by
        rw [← l35SlideOff M p hx, hxy]
        exact l35SlideSupport M p hy
      exact (hx (l35ExpandRange M p hr)).elim
    · exact M.vertex.injective (by simpa only [l35Slide, hx, hy, ite_false] using hxy)

private theorem l35SlideAdjacent {V W : Type} [DecidableEq V]
    {H : SimpleGraph V} {G : SimpleGraph W} (M : l35Model H G)
    {r t a b : V} (p : H.Walk r t) (hp : p.IsPath)
    (he : s(a, b) ∈ p.edges) : G.Adj (l35Slide M p a) (l35Slide M p b) := by
  obtain ⟨i, hi, he⟩ := p.mk_mem_edges_iff_exists.mp he
  have hi' : i + 1 ≤ p.length := by omega
  have hadj := (l35Expand M p).adj_getVert_succ (hi.trans_le (l35ExpandLength M p))
  have hs1 := l35SlideGetVert M p hp hi.le
  have hs2 := l35SlideGetVert M p hp hi'
  rcases Sym2.eq_iff.mp he with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · simpa only [← hs1, ← hs2, ha, hb] using hadj
  · simpa only [← hs1, ← hs2, ha, hb] using hadj.symm

private theorem l35SlideUnchanged {V W : Type} [DecidableEq V]
    {H : SimpleGraph V} {G : SimpleGraph W} (M : l35Model H G)
    {r t : V} (p : H.Walk r t) (hp : p.IsPath)
    (hclosed : ∀ x ∈ p.support, x ≠ r → ∀ y, H.Adj x y → s(x, y) ∈ p.edges)
    {a b : V} (hab : H.Adj a b) (he : s(a, b) ∉ p.edges) :
    l35Slide M p a = M.vertex a := by
  by_cases ha : a ∈ p.support
  · have har : a = r := by
      by_contra hn
      exact he (hclosed a ha hn b hab)
    rw [har]
    exact l35SlideRoot M p hp
  · exact l35SlideOff M p ha

private theorem l35ExpandAvoidRoute {V W : Type} {H : SimpleGraph V} {G : SimpleGraph W}
    (M : l35Model H G) {r t a b : V} (p : H.Walk r t) (hab : H.Adj a b)
    (he : s(a, b) ∉ p.edges) {x : W} (hx : x ∈ WalkInterior (M.route a b hab)) :
    x ∉ (l35Expand M p).support := by
  intro hs
  rcases l35ExpandSupport M p hs with ⟨c, _, hc⟩ | ⟨c, d, hcd, hcdp, hc⟩
  · exact M.avoid a b hab x hx ⟨c, hc.symm⟩
  · apply M.separate a b hab c d hcd x ?_ hx hc
    intro hsame
    exact he ((Sym2.eq_iff.mpr hsame).symm ▸ hcdp)

private theorem l35SlideAvoidRoute {V W : Type} [DecidableEq V]
    {H : SimpleGraph V} {G : SimpleGraph W} (M : l35Model H G)
    {r t a b : V} (p : H.Walk r t) (hab : H.Adj a b)
    (he : s(a, b) ∉ p.edges) {x : W} (hx : x ∈ WalkInterior (M.route a b hab)) :
    x ∉ Set.range (l35Slide M p) := by
  rintro ⟨c, rfl⟩
  by_cases hc : c ∈ p.support
  · exact l35ExpandAvoidRoute M p hab he hx (l35SlideSupport M p hc)
  · exact M.avoid a b hab _ hx ⟨c, (l35SlideOff M p hc).symm⟩

private def l35SlideRoute {V W : Type} [DecidableEq V]
    {H : SimpleGraph V} {G : SimpleGraph W} (M : l35Model H G)
    {r t : V} (p : H.Walk r t) (hp : p.IsPath)
    (hclosed : ∀ x ∈ p.support, x ≠ r → ∀ y, H.Adj x y → s(x, y) ∈ p.edges)
    (a b : V) (hab : H.Adj a b) : G.Walk (l35Slide M p a) (l35Slide M p b) :=
  if he : s(a, b) ∈ p.edges then (l35SlideAdjacent M p hp he).toWalk
  else (M.route a b hab).copy (l35SlideUnchanged M p hp hclosed hab he).symm
    (l35SlideUnchanged M p hp hclosed hab.symm
      (by simpa only [Sym2.eq_swap] using he)).symm

private theorem l35SlideRouteOldInterior {V W : Type} [DecidableEq V]
    {H : SimpleGraph V} {G : SimpleGraph W} (M : l35Model H G)
    {r t : V} (p : H.Walk r t) (hp : p.IsPath)
    (hclosed : ∀ x ∈ p.support, x ≠ r → ∀ y, H.Adj x y → s(x, y) ∈ p.edges)
    {a b : V} (hab : H.Adj a b) {x : W}
    (hx : x ∈ WalkInterior (l35SlideRoute M p hp hclosed a b hab)) :
    s(a, b) ∉ p.edges ∧ x ∈ WalkInterior (M.route a b hab) := by
  unfold l35SlideRoute at hx
  split_ifs at hx with he
  · simp only [WalkInterior, Set.mem_ofPred_eq, SimpleGraph.Adj.toWalk,
      SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hx
    exact (hx.1.elim hx.2.1 hx.2.2).elim
  · refine ⟨he, ?_⟩
    have ha := l35SlideUnchanged M p hp hclosed hab he
    have hb := l35SlideUnchanged M p hp hclosed hab.symm
      (by simpa only [Sym2.eq_swap] using he)
    simpa only [WalkInterior, Set.mem_ofPred_eq, SimpleGraph.Walk.support_copy,
      ha, hb] using hx

private theorem l35CompressArm {V W : Type} [DecidableEq V]
    {H : SimpleGraph V} {G : SimpleGraph W} (M : l35Model H G)
    {r t : V} (p : H.Walk r t) (hp : p.IsPath)
    (hclosed : ∀ x ∈ p.support, x ≠ r → ∀ y, H.Adj x y → s(x, y) ∈ p.edges) :
    ∃ N : l35Model H G,
      (∀ a b h, (N.route a b h).length ≤ (M.route a b h).length) ∧
      (∀ a b h, s(a, b) ∈ p.edges → (N.route a b h).length = 1) := by
  let N : l35Model H G := {
    vertex := ⟨l35Slide M p, l35SlideInjective M p hp⟩
    route := l35SlideRoute M p hp hclosed
    simple := by
      intro a b h
      unfold l35SlideRoute
      split_ifs
      · exact SimpleGraph.Adj.isPath_toWalk _
      · simpa only [SimpleGraph.Walk.isPath_copy] using M.simple a b h
    avoid := by
      intro a b hab x hx
      have hold := l35SlideRouteOldInterior M p hp hclosed hab hx
      exact l35SlideAvoidRoute M p hab hold.1 hold.2
    separate := by
      intro a b hab c d hcd x hne hx hy
      have hold := l35SlideRouteOldInterior M p hp hclosed hab hx
      have hold' := l35SlideRouteOldInterior M p hp hclosed hcd hy
      exact M.separate a b hab c d hcd x hne hold.2 hold'.2 }
  refine ⟨N, ?_, ?_⟩
  · intro a b hab
    change (l35SlideRoute M p hp hclosed a b hab).length ≤ _
    unfold l35SlideRoute
    split_ifs
    · have hpos : 0 < (M.route a b hab).length := Nat.pos_of_ne_zero fun h =>
        hab.ne (M.vertex.injective (SimpleGraph.Walk.eq_of_length_eq_zero h))
      simpa only [SimpleGraph.Adj.toWalk, SimpleGraph.Walk.length_cons,
        SimpleGraph.Walk.length_nil] using (Nat.succ_le_of_lt hpos)
    · simp only [SimpleGraph.Walk.length_copy, le_refl]
  · intro a b hab he
    change (l35SlideRoute M p hp hclosed a b hab).length = 1
    simp only [l35SlideRoute, he, dite_true, SimpleGraph.Adj.toWalk,
      SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil]

/- Minimizing total route length makes every non-internal edge a single edge. -/

private def l35ModelCost {V W : Type} [Fintype V] {H : SimpleGraph V}
    {G : SimpleGraph W} (M : l35Model H G) : ℕ := by
  classical
  exact ∑ e : V × V, if h : H.Adj e.1 e.2 then (M.route e.1 e.2 h).length else 0

private theorem l35ModelCostStrict {V W : Type} [Fintype V] {H : SimpleGraph V}
    {G : SimpleGraph W} (M N : l35Model H G)
    (hle : ∀ a b h, (N.route a b h).length ≤ (M.route a b h).length)
    {a b : V} (hab : H.Adj a b)
    (hlt : (N.route a b hab).length < (M.route a b hab).length) :
    l35ModelCost N < l35ModelCost M := by
  classical
  unfold l35ModelCost
  apply Finset.sum_lt_sum
  · intro e _
    split_ifs with h
    · exact hle _ _ h
    · exact Nat.le_refl 0
  · refine ⟨(a, b), Finset.mem_univ _, ?_⟩
    simpa only [hab, dite_true] using hlt

private theorem l35Normalize {V W : Type} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {G : SimpleGraph W} (M : l35Model H G) :
    ∃ N : l35Model H G, ∀ a b h, ¬ IsInternalEdge H a b →
      (N.route a b h).length = 1 := by
  classical
  have hex : ∃ n : ℕ, ∃ N : l35Model H G, l35ModelCost N = n :=
    ⟨l35ModelCost M, M, rfl⟩
  obtain ⟨N, hN⟩ := Nat.find_spec hex
  have hmin (N' : l35Model H G) : l35ModelCost N ≤ l35ModelCost N' := by
    rw [hN]
    exact Nat.find_min' hex ⟨N', rfl⟩
  refine ⟨N, ?_⟩
  intro a b hab hni
  by_contra hbad
  have hpos : 0 < (N.route a b hab).length :=
    Nat.pos_of_ne_zero fun h => hab.ne (N.vertex.injective
      (SimpleGraph.Walk.eq_of_length_eq_zero h))
  have hlong : 1 < (N.route a b hab).length := by omega
  have shrink (r u : V) (hru : H.Adj r u)
      (hbridge : ¬ (H.deleteEdges {Sym2.mk r u}).Reachable r u)
      (hlow : ∀ x, (H.deleteEdges {Sym2.mk r u}).Reachable u x → H.degree x ≤ 2)
      (hedge : Sym2.mk r u = Sym2.mk a b) : False := by
    obtain ⟨t, p, hp, hs, hmax⟩ := l35MaximalArm H hru
    have hclosed := l35ArmClosed hru hbridge hlow p hp hs hmax
    obtain ⟨N', hle, hshort⟩ := l35CompressArm N p hp hclosed
    have hem : Sym2.mk a b ∈ p.edges := by
      rw [← hedge]
      simpa only [hs] using p.mk_start_snd_mem_edges
        (by
          intro hnil
          cases hnil
          exact hru.ne hs)
    have hlt : (N'.route a b hab).length < (N.route a b hab).length := by
      rw [hshort a b hab hem]
      exact hlong
    exact (hmin N').not_gt (l35ModelCostStrict N N' hle hab hlt)
  have hbridge : ¬ (H.deleteEdges {Sym2.mk a b}).Reachable a b :=
    fun h => hni ⟨hab, Or.inl h⟩
  by_cases ha : ∃ x, (H.deleteEdges {Sym2.mk a b}).Reachable a x ∧ 3 ≤ H.degree x
  · apply shrink a b hab hbridge (hedge := rfl)
    intro x hx
    by_contra hn
    exact hni ⟨hab, Or.inr ⟨ha, x, hx, by omega⟩⟩
  · apply shrink b a hab.symm
    · intro h
      exact hbridge (by simpa only [Sym2.eq_swap] using h.symm)
    · intro x hx
      by_contra hn
      exact ha ⟨x, by simpa only [Sym2.eq_swap] using hx, by omega⟩
    · exact Sym2.eq_swap

/- Restrict a bounded model to its finite support and relabel that support by Fin. -/
private theorem l35InduceSupport {V : Type} {G : SimpleGraph V} {s : Set V}
    {u v : V} (p : G.Walk u v) (hp : ∀ x ∈ p.support, x ∈ s) {x : s}
    (hx : x ∈ (p.induce s hp).support) : x.val ∈ p.support := by
  have hx' : x.val ∈ ((p.induce s hp).map
      (SimpleGraph.Embedding.induce s).toHom).support := by
    rw [SimpleGraph.Walk.support_map]
    exact List.mem_map.mpr ⟨x, hx, rfl⟩
  simpa only [SimpleGraph.Walk.map_induce] using hx'

private theorem l35RestrictModel {V W : Type} {H : SimpleGraph V} {G : SimpleGraph W}
    (M : l35Model H G) (s : Set W) (hvertex : ∀ a, M.vertex a ∈ s)
    (hroute : ∀ a b h x, x ∈ (M.route a b h).support → x ∈ s) :
    ContainsTopologicalMinor H (G.induce s) := by
  let φ : V ↪ s := ⟨fun a => ⟨M.vertex a, hvertex a⟩,
    fun _ _ h => M.vertex.injective (congrArg Subtype.val h)⟩
  refine ⟨φ, fun a b h => (M.route a b h).induce s (hroute a b h), ?_, ?_⟩
  · intro a b h x hx ⟨c, hc⟩
    apply M.avoid a b h x.val
      ⟨l35InduceSupport _ _ hx.1, ?_, ?_⟩ ⟨c, congrArg Subtype.val hc⟩
    · exact fun he => hx.2.1 (Subtype.ext he)
    · exact fun he => hx.2.2 (Subtype.ext he)
  · intro a b hab c d hcd x hne hx hy
    apply M.separate a b hab c d hcd x.val hne
      ⟨l35InduceSupport _ _ hx.1, ?_, ?_⟩
      ⟨l35InduceSupport _ _ hy.1, ?_, ?_⟩
    · exact fun he => hx.2.1 (Subtype.ext he)
    · exact fun he => hx.2.2 (Subtype.ext he)
    · exact fun he => hy.2.1 (Subtype.ext he)
    · exact fun he => hy.2.2 (Subtype.ext he)

private theorem l35BoundedWitness {m : ℕ} {W : Type}
    {H : SimpleGraph (Fin m)} {G : SimpleGraph W} (M : l35Model H G)
    (L : ℕ) (hL : ∀ a b h, (M.route a b h).length ≤ L) :
    ∃ r ≤ m + m * m * (L + 1), ∃ K : SimpleGraph (Fin r),
      ContainsTopologicalMinor H K ∧ ContainsSubgraph K G := by
  classical
  let t : Fin m × Fin m → Finset W := fun e =>
    if h : H.Adj e.1 e.2 then (M.route e.1 e.2 h).support.toFinset else ∅
  let branches : Finset W := Finset.univ.image M.vertex
  let routes : Finset W := Finset.univ.biUnion t
  let s : Finset W := branches ∪ routes
  have hbranches : branches.card ≤ m := by
    simpa only [branches, Finset.card_univ, Fintype.card_fin] using
      (Finset.card_image_le (s := (Finset.univ : Finset (Fin m))) (f := M.vertex))
  have ht (e : Fin m × Fin m) : (t e).card ≤ L + 1 := by
    dsimp only [t]
    split_ifs with h
    · exact (List.toFinset_card_le _).trans (by
        simpa only [SimpleGraph.Walk.length_support] using Nat.add_le_add_right (hL _ _ h) 1)
    · simp
  have hroutes : routes.card ≤ m * m * (L + 1) := by
    calc
      routes.card ≤ ∑ e : Fin m × Fin m, (t e).card := Finset.card_biUnion_le
      _ ≤ ∑ _e : Fin m × Fin m, (L + 1) := Finset.sum_le_sum (fun e _ => ht e)
      _ = m * m * (L + 1) := by simp
  have hs : s.card ≤ m + m * m * (L + 1) :=
    (Finset.card_union_le branches routes).trans (Nat.add_le_add hbranches hroutes)
  have hvertex (a : Fin m) : M.vertex a ∈ s :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)
  have hroute (a b : Fin m) (h : H.Adj a b) (x : W)
      (hx : x ∈ (M.route a b h).support) : x ∈ s := by
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨(a, b), Finset.mem_univ _, ?_⟩
    simpa only [t, h, dite_true, List.mem_toFinset] using hx
  let K₀ : SimpleGraph s := G.induce (s : Set W)
  have htop : ContainsTopologicalMinor H K₀ := l35RestrictModel M _ hvertex hroute
  let e := Fintype.equivFin s
  let K : SimpleGraph (Fin (Fintype.card s)) := K₀.comap e.symm
  refine ⟨Fintype.card s, ?_, K, ?_, ?_⟩
  · simpa only [Fintype.card_coe] using hs
  · apply l35TopologicalTrans htop
    apply l35SubgraphTopological
    refine ⟨e.toEmbedding, ?_⟩
    intro a b hab
    change K₀.Adj (e.symm (e a)) (e.symm (e b))
    simpa only [Equiv.symm_apply_apply] using hab
  · refine ⟨e.symm.toEmbedding.trans (Function.Embedding.subtype (fun x => x ∈ s)), ?_⟩
    intro a b hab
    exact hab

/- Mixed descriptions retain a topological part and an equivalent subgraph part. -/

private theorem l35DeletedMap {V W : Type} {H : SimpleGraph V} {G : SimpleGraph W}
    (e : H ≃g G) {u v a b : V}
    (h : (H.deleteEdges {s(u, v)}).Reachable a b) :
    (G.deleteEdges {s(e u, e v)}).Reachable (e a) (e b) := by
  let f : H.deleteEdges {s(u, v)} →g G.deleteEdges {s(e u, e v)} := {
    toFun := e
    map_rel' := by
      intro x y hxy
      obtain ⟨hxy, hne⟩ := SimpleGraph.deleteEdges_adj.mp hxy
      refine SimpleGraph.deleteEdges_adj.mpr ⟨e.map_adj_iff.mpr hxy, ?_⟩
      simpa only [Set.mem_singleton_iff, Sym2.eq_iff, e.injective.eq_iff] using hne }
  exact h.map f

private theorem l35InternalMap {V W : Type} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] {H : SimpleGraph V} {G : SimpleGraph W}
    (e : H ≃g G) {u v : V} (h : IsInternalEdge H u v) :
    IsInternalEdge G (e u) (e v) := by
  classical
  refine ⟨e.map_adj_iff.mpr h.1, ?_⟩
  rcases h.2 with hc | ⟨⟨a, ha, hda⟩, ⟨b, hb, hdb⟩⟩
  · exact Or.inl (l35DeletedMap e hc)
  · exact Or.inr ⟨⟨e a, l35DeletedMap e ha, by simpa using hda⟩,
      ⟨e b, l35DeletedMap e hb, by simpa using hdb⟩⟩

private theorem l35BetaIsoLe {V W : Type} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] {H : SimpleGraph V} {G : SimpleGraph W}
    (e : H ≃g G) : beta H ≤ beta G := by
  classical
  unfold beta
  apply Finset.card_le_card_of_injOn e.toEquiv.toEmbedding.sym2Map
  · intro q hq
    obtain ⟨_, a, b, rfl, hab⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr
      ⟨SimpleGraph.mem_edgeFinset.mpr (e.map_adj_iff.mpr hab.1),
        e a, e b, rfl, l35InternalMap e hab⟩
  · intro a _ b _ hab
    exact e.toEquiv.toEmbedding.sym2Map.injective hab

private theorem l35BetaIso {V W : Type} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] {H : SimpleGraph V} {G : SimpleGraph W}
    (e : H ≃g G) : beta H = beta G :=
  Nat.le_antisymm (l35BetaIsoLe e) (l35BetaIsoLe e.symm)

private theorem l35IsoSubgraph {V W : Type} {H : SimpleGraph V} {G : SimpleGraph W}
    (e : H ≃g G) : ContainsSubgraph H G :=
  ⟨e.toEquiv.toEmbedding, fun {_ _} h => e.map_adj_iff.mpr h⟩

private def TMEquiv (B : Finset (Sigma fun k : ℕ => SimpleGraph (Fin k))) : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W] (G : SimpleGraph W),
    (∃ b ∈ B, ContainsTopologicalMinor b.2 G) ↔
      (∃ b ∈ B, ContainsSubgraph b.2 G)

private def ValidDesc (P : GraphProperty)
    (S B : Finset (Sigma fun k : ℕ => SimpleGraph (Fin k))) : Prop :=
  TMEquiv B ∧ ∀ (W : Type) [Fintype W] [DecidableEq W] (G : SimpleGraph W),
    P W G ↔ (∀ s ∈ S, ¬ ContainsTopologicalMinor s.2 G) ∧
      (∀ b ∈ B, ¬ ContainsSubgraph b.2 G)

private theorem l35BetaLe {m : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (H : SimpleGraph (Fin m)) (G : SimpleGraph W)
    (h : ContainsTopologicalMinor H G) : beta H ≤ beta G := by
  classical
  let e := (Fintype.equivFin W).symm
  let K := G.comap e
  let i : K ≃g G := SimpleGraph.Iso.comap e G
  have hk : ContainsTopologicalMinor H K :=
    l35TopologicalTrans h (l35SubgraphTopological (l35IsoSubgraph i.symm))
  exact (lemma32 H K hk).trans_eq (l35BetaIso i)

private theorem l35Initial (P : GraphProperty) (h : DescribedByForbiddenTopologicalMinors P) :
    ∃ S B, ValidDesc P S B := by
  classical
  obtain ⟨F, hF⟩ := h
  refine ⟨F, ∅, ?_, ?_⟩
  · intro W _ _ G
    simp
  · intro W _ _ G
    simpa using hF W G

private theorem l35TransferZero (P : GraphProperty)
    (S B : Finset (Sigma fun k : ℕ => SimpleGraph (Fin k)))
    (hd : ValidDesc P S B) (s : Sigma fun k : ℕ => SimpleGraph (Fin k))
    (hs : s ∈ S)
    (hzero : beta s.2 = 0) : ValidDesc P (S.erase s) (insert s B) := by
  classical
  have heq := (lemma34 s.2).mpr hzero
  refine ⟨?_, ?_⟩
  · intro W _ _ G
    simp only [Finset.exists_mem_insert]
    rw [heq W G, hd.1 W G]
  · intro W _ _ G
    rw [hd.2 W G]
    constructor
    · rintro ⟨hS, hB⟩
      refine ⟨fun t ht => hS t (Finset.mem_of_mem_erase ht), ?_⟩
      intro b hb hbg
      rcases Finset.mem_insert.mp hb with hb | hb
      · subst b
        exact hS s hs ((heq W G).mpr hbg)
      · exact hB b hb hbg
    · rintro ⟨hS, hB⟩
      refine ⟨?_, fun b hb => hB b (Finset.mem_insert_of_mem hb)⟩
      intro t ht htG
      by_cases hts : t = s
      · subst t
        exact hB s (Finset.mem_insert_self _ _) ((heq W G).mp htG)
      · exact hS t (Finset.mem_erase.mpr ⟨hts, ht⟩) htG

private theorem l35Replace (P : GraphProperty)
    (S B K : Finset (Sigma fun k : ℕ => SimpleGraph (Fin k)))
    (hd : ValidDesc P S B) (s : Sigma fun k : ℕ => SimpleGraph (Fin k)) (hs : s ∈ S)
    (hK : ∀ k ∈ K, ContainsTopologicalMinor s.2 k.2)
    (hcover : ∀ (W : Type) [Fintype W] [DecidableEq W] (G : SimpleGraph W),
      ContainsTopologicalMinor s.2 G →
      ¬ (∃ b ∈ B, ContainsTopologicalMinor b.2 G) →
      ∃ k ∈ K, ContainsSubgraph k.2 G) : ValidDesc P (S.erase s) (B ∪ K) := by
  classical
  have convert (W : Type) [Fintype W] [DecidableEq W] (G : SimpleGraph W)
      (h : ∃ b ∈ B ∪ K, ContainsTopologicalMinor b.2 G) :
      ∃ b ∈ B ∪ K, ContainsSubgraph b.2 G := by
    obtain ⟨b, hb, hbg⟩ := h
    by_cases hB : ∃ b ∈ B, ContainsTopologicalMinor b.2 G
    · obtain ⟨c, hc, hcG⟩ := (hd.1 W G).mp hB
      exact ⟨c, Finset.mem_union_left _ hc, hcG⟩
    · have hbK : b ∈ K := (Finset.mem_union.mp hb).resolve_left
        (fun hb => hB ⟨b, hb, hbg⟩)
      obtain ⟨c, hc, hcG⟩ := hcover W G (l35TopologicalTrans (hK b hbK) hbg) hB
      exact ⟨c, Finset.mem_union_right _ hc, hcG⟩
  refine ⟨?_, ?_⟩
  · intro W _ _ G
    exact ⟨convert W G, fun ⟨b, hb, hbg⟩ => ⟨b, hb, l35SubgraphTopological hbg⟩⟩
  · intro W _ _ G
    rw [hd.2 W G]
    constructor
    · rintro ⟨hS, hB⟩
      refine ⟨fun t ht => hS t (Finset.mem_of_mem_erase ht), ?_⟩
      intro b hb hbg
      rcases Finset.mem_union.mp hb with hb | hb
      · exact hB b hb hbg
      · exact hS s hs (l35TopologicalTrans (hK b hb) (l35SubgraphTopological hbg))
    · rintro ⟨hS, hB⟩
      refine ⟨?_, fun b hb => hB b (Finset.mem_union_left _ hb)⟩
      intro t ht htG
      by_cases hts : t = s
      · subst t
        have hex : ∃ b ∈ B ∪ K, ContainsTopologicalMinor b.2 G := by
          by_cases hBT : ∃ b ∈ B, ContainsTopologicalMinor b.2 G
          · obtain ⟨b, hb, hbG⟩ := hBT
            exact ⟨b, Finset.mem_union_left _ hb, hbG⟩
          · obtain ⟨b, hb, hbG⟩ := hcover W G htG hBT
            exact ⟨b, Finset.mem_union_right _ hb, l35SubgraphTopological hbG⟩
        obtain ⟨b, hb, hbG⟩ := convert W G hex
        exact hB b hb hbG
      · exact hS t (Finset.mem_erase.mpr ⟨hts, ht⟩) htG

/-- Lemma 3.5: every non-FSP property described by finitely many forbidden
topological minors admits a forbidden graph `G` and an edge `(u, v)` satisfying
`SplitsInto P G u v`. -/
theorem lemma35 (P : GraphProperty) (hdesc : DescribedByForbiddenTopologicalMinors P)
    (hnot : ¬ IsFSP P) :
    ∃ (k : ℕ) (G : SimpleGraph (Fin k)) (u v : Fin k),
      ¬ P (Fin k) G ∧ G.Adj u v ∧ SplitsInto P G u v := by
  classical
  have hex : ∃ c : ℕ, ∃ S B, ValidDesc P S B ∧ S.card = c := by
    obtain ⟨S, B, hd⟩ := l35Initial P hdesc
    exact ⟨S.card, S, B, hd, rfl⟩
  obtain ⟨S, B, hd, hcard⟩ := Nat.find_spec hex
  have hmin (T C : Finset (Sigma fun k : ℕ => SimpleGraph (Fin k)))
      (ht : ValidDesc P T C) : S.card ≤ T.card := by
    rw [hcard]
    exact Nat.find_min' hex ⟨T, C, ht, rfl⟩
  have hSne : S.Nonempty := by
    by_contra hn
    have hS : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    apply hnot
    refine ⟨B, ?_⟩
    intro W _ _ G
    simpa only [hS, Finset.notMem_empty, false_implies, implies_true, forall_const,
      true_and] using hd.2 W G
  obtain ⟨s, hs, hbeta⟩ := S.exists_min_image (fun t => beta t.2) hSne
  by_cases hzero : beta s.2 = 0
  · have hle := hmin (S.erase s) (insert s B) (l35TransferZero P S B hd s hs hzero)
    have hlt := Finset.card_erase_lt_of_mem hs
    omega
  have hself : ContainsTopologicalMinor s.2 s.2 :=
    l35SubgraphTopological ⟨Function.Embedding.refl _, fun {_ _} h => h⟩
  have hbad : ¬ P (Fin s.1) s.2 := fun h => (hd.2 (Fin s.1) s.2).mp h |>.1 s hs hself
  by_contra hresult
  have hnosplit (u v : Fin s.1) (hi : IsInternalEdge s.2 u v) :
      ¬ SplitsInto P s.2 u v := fun h => hresult ⟨s.1, s.2, u, v, hbad, hi.1, h⟩
  let I := {e : Fin s.1 × Fin s.1 // IsInternalEdge s.2 e.1 e.2}
  have badSplit (e : I) : ∃ n₁ n₂ : ℕ,
      ∃ b ∈ B, ContainsSubgraph b.2 (twoPathSplitSum s.2 e.val.1 e.val.2 n₁ n₂) := by
    obtain ⟨n₁, n₂, hn⟩ : ∃ n₁ n₂ : ℕ,
        ¬ P _ (twoPathSplitSum s.2 e.val.1 e.val.2 n₁ n₂) := by
      simpa only [SplitsInto, not_forall] using hnosplit _ _ e.property
    refine ⟨n₁, n₂, ?_⟩
    by_contra hnB
    apply hn
    apply (hd.2 _ _).mpr
    refine ⟨?_, ?_⟩
    · intro t ht htG
      have hle := l35BetaLe t.2 _ htG
      have hlt := lemma33 s.2 e.property n₁ n₂
      have hminbeta := hbeta t ht
      omega
    · intro b hb hbG
      exact hnB ⟨b, hb, hbG⟩
  choose n₁ n₂ b hb hbG using badSplit
  let L : ℕ := 1 + ∑ e : I, (n₁ e + n₂ e + 2)
  have hLpos : 1 ≤ L := by unfold L; omega
  have hlength (e : I) : n₁ e + n₂ e + 1 < L := by
    have hsum := Finset.single_le_sum
      (fun f (_ : f ∈ (Finset.univ : Finset I)) => Nat.zero_le (n₁ f + n₂ f + 2))
      (Finset.mem_univ e)
    unfold L
    omega
  let R := s.1 + s.1 * s.1 * (L + 1)
  let Kset : Finset (Sigma fun k : ℕ => SimpleGraph (Fin k)) :=
    ((Finset.range (R + 1)).sigma (fun r =>
      (Finset.univ : Finset (SimpleGraph (Fin r))))).filter
        (fun k => ContainsTopologicalMinor s.2 k.2)
  have hK (k : Sigma fun k : ℕ => SimpleGraph (Fin k)) (hk : k ∈ Kset) :
      ContainsTopologicalMinor s.2 k.2 := (Finset.mem_filter.mp hk).2
  have hcover (W : Type) [Fintype W] [DecidableEq W] (G : SimpleGraph W)
      (hsg : ContainsTopologicalMinor s.2 G)
      (hB : ¬ (∃ b ∈ B, ContainsTopologicalMinor b.2 G)) :
      ∃ k ∈ Kset, ContainsSubgraph k.2 G := by
    obtain ⟨M⟩ := l35SimpleModel hsg
    obtain ⟨N, hshort⟩ := l35Normalize M
    have hbound (u v : Fin s.1) (huv : s.2.Adj u v) : (N.route u v huv).length ≤ L := by
      by_cases hi : IsInternalEdge s.2 u v
      · by_contra hlong
        let e : I := ⟨(u, v), hi⟩
        have hsplit := l35LongSplit N huv (n₁ e) (n₂ e)
          ((hlength e).trans (Nat.lt_of_not_ge hlong))
        exact hB ⟨b e, hb e, l35TopologicalTrans (l35SubgraphTopological (hbG e)) hsplit⟩
      · rw [hshort u v huv hi]
        exact hLpos
    obtain ⟨r, hr, K, htop, hsub⟩ := l35BoundedWitness N L hbound
    refine ⟨⟨r, K⟩, ?_, hsub⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, htop⟩
    apply Finset.mem_sigma.mpr
    exact ⟨Finset.mem_range.mpr (by change r < R + 1; omega), Finset.mem_univ K⟩
  have hnew := l35Replace P S B Kset hd s hs hK hcover
  have hle := hmin (S.erase s) (B ∪ Kset) hnew
  have hlt := Finset.card_erase_lt_of_mem hs
  omega

end Qatlib.Papers.MinorClosed10.MainResults.Source
