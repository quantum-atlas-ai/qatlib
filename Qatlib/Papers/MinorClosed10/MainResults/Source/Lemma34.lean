/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MinorClosed10.MainResults.Model.PaperObjects

set_option backward.isDefEq.respectTransparency false

/-!
# Characterization of Subgraph and Topological-Minor Equivalence

This module formalizes Lemma 3.4 of Childs and Kothari showing that for any
finite graph `H`, topological-minor containment of `H` coincides with subgraph
containment of `H` across all finite host graphs if and only if the internal-edge
parameter `β(H)` vanishes.

## Main statements

* `lemma34`: Lemma 3.4, proving that `(∀ G, ContainsTopologicalMinor H G ↔ ContainsSubgraph H G) ↔ beta H = 0`.

## References

* [Childs and Kothari, 2012][ChildsKothari2012], Section 3, Lemma 3.4, p. 10.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MinorClosed10.MainResults.Source

open Qatlib.Papers.MinorClosed10.MainResults

private theorem l34Structure_noInternal {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) : beta H = 0 ↔ ∀ u v, ¬ IsInternalEdge H u v := by
  classical
  constructor
  · intro h u v huv
    have hempty := Finset.card_eq_zero.mp h
    have hmem : Sym2.mk u v ∈ H.edgeFinset.filter
        (fun e => ∃ a b, e = Sym2.mk a b ∧ IsInternalEdge H a b) := by
      exact Finset.mem_filter.mpr
        ⟨SimpleGraph.mem_edgeFinset.mpr huv.1, u, v, rfl, huv⟩
    rw [hempty] at hmem
    exact Finset.notMem_empty _ hmem
  · intro h
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨_, u, v, _, huv⟩ := Finset.mem_filter.mp he
    exact h u v huv

private theorem l34Structure_acyclic {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (hbeta : beta H = 0) : H.IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  intro u v huv
  rw [SimpleGraph.isBridge_iff]
  intro hr
  exact (l34Structure_noInternal H).mp hbeta u v ⟨huv, Or.inl hr⟩

open scoped Classical in
private theorem l34Structure_branch_unique {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (hbeta : beta H = 0) {u v : V}
    (hreach : H.Reachable u v) (hu : 3 ≤ H.degree u) (hv : 3 ≤ H.degree v) :
    u = v := by
  classical
  apply hreach.elim_path
  intro p
  obtain ⟨p, hp⟩ := p
  cases p with
  | nil => rfl
  | @cons u w v huw p =>
    have hedge : Sym2.mk u w ∉ p.edges :=
      ((SimpleGraph.Walk.isTrail_cons huw p).mp hp.isTrail).2
    have htail : (H.deleteEdges {Sym2.mk u w}).Reachable w v :=
      SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr ⟨p, hedge⟩
    exact False.elim <| (l34Structure_noInternal H).mp hbeta u w
      ⟨huw, Or.inr ⟨⟨u, .rfl, hu⟩, ⟨v, htail, hv⟩⟩⟩

private def l34Structure_componentRoot {V : Type}
    (H : SimpleGraph V) (C : H.ConnectedComponent) : V := by
  classical
  exact if h : ∃ a, H.connectedComponentMk a = C ∧ 3 ≤ (H.neighborSet a).ncard then
    h.choose else C.exists_rep.choose

private theorem l34Structure_componentRoot_spec {V : Type}
    (H : SimpleGraph V) (C : H.ConnectedComponent) :
    H.connectedComponentMk (l34Structure_componentRoot H C) = C := by
  classical
  unfold l34Structure_componentRoot
  split_ifs with h
  · exact h.choose_spec.1
  · exact C.exists_rep.choose_spec

private def l34Structure_root {V : Type} (H : SimpleGraph V) (x : V) : V :=
  l34Structure_componentRoot H (H.connectedComponentMk x)

private theorem l34Structure_root_reachable {V : Type}
    (H : SimpleGraph V) (x : V) : H.Reachable (l34Structure_root H x) x :=
  SimpleGraph.ConnectedComponent.exact (l34Structure_componentRoot_spec H _)

private theorem l34Structure_root_eq {V : Type}
    (H : SimpleGraph V) {x y : V} (h : H.Reachable x y) :
    l34Structure_root H x = l34Structure_root H y :=
  congrArg (l34Structure_componentRoot H) (SimpleGraph.ConnectedComponent.sound h)

open scoped Classical in
private theorem l34Structure_degree_le_two {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (hbeta : beta H = 0) {x : V}
    (hx : x ≠ l34Structure_root H x) : H.degree x ≤ 2 := by
  classical
  by_contra hn
  have hdeg : 3 ≤ H.degree x := by omega
  have hex : ∃ a, H.connectedComponentMk a = H.connectedComponentMk x ∧
      3 ≤ (H.neighborSet a).ncard := ⟨x, rfl, by simpa only [SimpleGraph.ncard_neighborSet]⟩
  have hroot : 3 ≤ H.degree (l34Structure_root H x) := by
    rw [← SimpleGraph.ncard_neighborSet]
    unfold l34Structure_root l34Structure_componentRoot
    simpa only [hex, dite_true] using hex.choose_spec.2
  exact hx (l34Structure_branch_unique H hbeta
    (l34Structure_root_reachable H x).symm hdeg hroot)

private theorem l34Structure_adj_paths {V : Type} {H : SimpleGraph V}
    (ha : H.IsAcyclic) {r x y : V} {p : H.Walk r x} {q : H.Walk r y}
    (hp : p.IsPath) (hq : q.IsPath) (hxy : H.Adj x y) :
    q = p.concat hxy ∨ p = q.concat hxy.symm := by
  classical
  by_cases hx : x ∈ q.support
  · exact Or.inl (ha.path_concat hp hq hxy hx)
  · have hy : y ∈ p.support :=
      ha.mem_support_of_ne_mem_support_of_adj_of_isPath hp hq hxy hx
    exact Or.inr (ha.path_concat hq hp hxy.symm hy)

private theorem l34Structure_paths_unique {V : Type} {H : SimpleGraph V}
    (ha : H.IsAcyclic) {r x : V} {p q : H.Walk r x} (hp : p.IsPath) (hq : q.IsPath) :
    p = q :=
  congrArg Subtype.val ((ha.subsingleton_path r x).elim ⟨p, hp⟩ ⟨q, hq⟩)

private theorem l34Structure_snd_concat {V : Type} {H : SimpleGraph V}
    {r x y : V} (p : H.Walk r x) (hxy : H.Adj x y) (hx : x ≠ r) :
    (p.concat hxy).snd = p.snd := by
  cases p with
  | nil => exact (hx rfl).elim
  | cons => simp only [SimpleGraph.Walk.concat_cons, SimpleGraph.Walk.snd_cons]

private theorem l34Structure_closed_path_eq_nil {V : Type} {H : SimpleGraph V}
    {r : V} {p : H.Walk r r} (hp : p.IsPath) : p = .nil :=
  (SimpleGraph.Walk.isPath_iff_nil.mp hp).eq_nil

open scoped Classical in
private theorem l34Structure_of_acyclic_branch_unique {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (ha : H.IsAcyclic)
    (hb : ∀ a b : V, H.Reachable a b → 3 ≤ H.degree a → 3 ≤ H.degree b → a = b) :
    beta H = 0 := by
  classical
  apply (l34Structure_noInternal H).mpr
  intro u v huv
  obtain ⟨huv, hc | ⟨⟨a, hua, hda⟩, ⟨b, hvb, hdb⟩⟩⟩ := huv
  · exact (SimpleGraph.isBridge_iff.mp
      (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp ha huv)) hc
  · have hab : H.Reachable a b :=
      ((hua.mono (H.deleteEdges_le _)).symm.trans huv.reachable).trans
        (hvb.mono (H.deleteEdges_le _))
    have heq := hb a b hab hda hdb
    subst b
    exact (SimpleGraph.isBridge_iff.mp
      (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp ha huv)) (hua.trans hvb.symm)

private def l34Expand {V W : Type} {H : SimpleGraph V} {G : SimpleGraph W}
    (φ : V ↪ W) (P : ∀ a b, H.Adj a b → G.Walk (φ a) (φ b))
    {a b : V} : H.Walk a b → G.Walk (φ a) (φ b)
  | .nil => .nil
  | .cons hab p => (P _ _ hab).append (l34Expand φ P p)

private theorem l34ExpandSupport {V W : Type} {H : SimpleGraph V} {G : SimpleGraph W}
    (φ : V ↪ W) (P : ∀ a b, H.Adj a b → G.Walk (φ a) (φ b))
    {a b : V} (p : H.Walk a b) {x : W} (hx : x ∈ (l34Expand φ P p).support) :
    (∃ c ∈ p.support, x = φ c) ∨
      ∃ c d, ∃ h : H.Adj c d, Sym2.mk c d ∈ p.edges ∧ x ∈ WalkInterior (P c d h) := by
  induction p with
  | @nil a =>
    exact .inl ⟨a, by simp, by simpa [l34Expand] using hx⟩
  | @cons a b c hab p ih =>
    rw [l34Expand, SimpleGraph.Walk.mem_support_append_iff] at hx
    rcases hx with hx | hx
    · by_cases ha : x = φ a
      · exact .inl ⟨a, by simp, ha⟩
      by_cases hb : x = φ b
      · exact .inl ⟨b, by simp, hb⟩
      exact .inr ⟨a, b, hab, by simp, hx, ha, hb⟩
    · rcases ih hx with ⟨d, hd, hxd⟩ | ⟨d, e, hde, he, hx⟩
      · exact .inl ⟨d, by simp [hd], hxd⟩
      · exact .inr ⟨d, e, hde, by simp [he], hx⟩

private theorem l34ExpandRange {V W : Type} {H : SimpleGraph V} {G : SimpleGraph W}
    (φ : V ↪ W) (P : ∀ a b, H.Adj a b → G.Walk (φ a) (φ b))
    (havoid : ∀ a b (h : H.Adj a b) x, x ∈ WalkInterior (P a b h) → x ∉ Set.range φ)
    {a b c : V} (p : H.Walk a b) (hc : φ c ∈ (l34Expand φ P p).support) :
    c ∈ p.support := by
  rcases l34ExpandSupport φ P p hc with ⟨d, hd, hcd⟩ | ⟨d, e, hde, _, hx⟩
  · exact (φ.injective hcd).symm ▸ hd
  · exact (havoid d e hde _ hx ⟨c, rfl⟩).elim

private theorem l34ExpandLength {V W : Type} {H : SimpleGraph V} {G : SimpleGraph W}
    (φ : V ↪ W) (P : ∀ a b, H.Adj a b → G.Walk (φ a) (φ b))
    {a b : V} (p : H.Walk a b) : p.length ≤ (l34Expand φ P p).length := by
  induction p with
  | nil => exact Nat.le_refl 0
  | @cons a b c hab p ih =>
    have hpos : 0 < (P a b hab).length := Nat.pos_of_ne_zero fun h =>
      hab.ne (φ.injective (SimpleGraph.Walk.eq_of_length_eq_zero h))
    simp only [l34Expand, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons]
    omega

private theorem l34ExpandMeet {V W : Type} {H : SimpleGraph V} {G : SimpleGraph W}
    (φ : V ↪ W) (P : ∀ a b, H.Adj a b → G.Walk (φ a) (φ b))
    (havoid : ∀ a b (h : H.Adj a b) x, x ∈ WalkInterior (P a b h) → x ∉ Set.range φ)
    (hdisjoint : ∀ a b (hab : H.Adj a b) c d (hcd : H.Adj c d) x,
      ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) →
      x ∈ WalkInterior (P a b hab) → x ∈ WalkInterior (P c d hcd) → False)
    {a b c d : V} (p : H.Walk a b) (q : H.Walk c d) (r : V)
    (hcommon : ∀ z, z ∈ p.support → z ∈ q.support → z = r)
    {x : W} (hp : x ∈ (l34Expand φ P p).support)
    (hq : x ∈ (l34Expand φ P q).support) : x = φ r := by
  rcases l34ExpandSupport φ P p hp with ⟨u, hu, rfl⟩ | ⟨u, v, huv, he, hx⟩
  · exact congrArg φ (hcommon u hu (l34ExpandRange φ P havoid q hq))
  rcases l34ExpandSupport φ P q hq with ⟨u', _, heq⟩ | ⟨u', v', huv', he', hx'⟩
  · exact (havoid u v huv x hx ⟨u', heq.symm⟩).elim
  by_cases hsame : (u = u' ∧ v = v') ∨ (u = v' ∧ v = u')
  · have hu := p.fst_mem_support_of_mem_edges he
    have hv := p.snd_mem_support_of_mem_edges he
    have hu' := q.fst_mem_support_of_mem_edges he'
    have hv' := q.snd_mem_support_of_mem_edges he'
    rcases hsame with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (huv.ne ((hcommon _ hu hu').trans (hcommon _ hv hv').symm)).elim
    · exact (huv.ne ((hcommon _ hu hv').trans (hcommon _ hv hu').symm)).elim
  · exact (hdisjoint u v huv u' v' huv' x hsame hx hx').elim

private theorem l34PathEndNotDropLast {V : Type} {H : SimpleGraph V} {a b : V}
    (p : H.Walk a b) (hp : p.IsPath) : b ∉ p.support.dropLast := by
  intro hb
  have hnodup := hp.support_nodup
  rw [← p.dropLast_support_concat] at hnodup
  exact List.disjoint_of_nodup_append hnodup hb (by simp)

private theorem l34ExpandPath {V W : Type} {H : SimpleGraph V} {G : SimpleGraph W}
    (φ : V ↪ W) (P : ∀ a b, H.Adj a b → G.Walk (φ a) (φ b))
    (hpath : ∀ a b (h : H.Adj a b), (P a b h).IsPath)
    (havoid : ∀ a b (h : H.Adj a b) x, x ∈ WalkInterior (P a b h) → x ∉ Set.range φ)
    (hdisjoint : ∀ a b (hab : H.Adj a b) c d (hcd : H.Adj c d) x,
      ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) →
      x ∈ WalkInterior (P a b hab) → x ∈ WalkInterior (P c d hcd) → False)
    {a b : V} (p : H.Walk a b) (hp : p.IsPath) : (l34Expand φ P p).IsPath := by
  induction p with
  | nil => exact .nil
  | @cons a b c hab p ih =>
    have hp' := (SimpleGraph.Walk.cons_isPath_iff hab p).mp hp
    rw [l34Expand, SimpleGraph.Walk.isPath_append']
    refine ⟨(hpath a b hab).dropLast, ih hp'.1, ?_⟩
    intro x hx hy
    have hx' := List.mem_of_mem_dropLast hx
    have hmeet : x = φ b := by
      apply l34ExpandMeet φ P havoid hdisjoint (.cons hab .nil) p b
      · intro z hz hz'
        simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
          List.mem_cons, List.not_mem_nil, or_false] at hz
        exact hz.resolve_left (fun h => hp'.2 (h ▸ hz'))
      · simpa [l34Expand] using hx'
      · exact hy
    exact l34PathEndNotDropLast (P a b hab) (hpath a b hab) (hmeet ▸ hx)

private theorem l34SimpleModel {V W : Type} {H : SimpleGraph V} {G : SimpleGraph W}
    (h : ContainsTopologicalMinor H G) :
    ∃ (φ : V ↪ W) (P : ∀ a b, H.Adj a b → G.Walk (φ a) (φ b)),
      (∀ a b (hab : H.Adj a b), (P a b hab).IsPath) ∧
      (∀ a b (hab : H.Adj a b) x, x ∈ WalkInterior (P a b hab) → x ∉ Set.range φ) ∧
      (∀ a b (hab : H.Adj a b) c d (hcd : H.Adj c d) x,
        ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) →
        x ∈ WalkInterior (P a b hab) → x ∈ WalkInterior (P c d hcd) → False) := by
  classical
  obtain ⟨φ, P, havoid, hdisjoint⟩ := h
  refine ⟨φ, fun a b hab => (P a b hab).toPath, fun a b hab => (P a b hab).toPath.isPath,
    ?_, ?_⟩
  · intro a b hab x hx
    exact havoid a b hab x
      ⟨(P a b hab).support_toPath_subset_support hx.1, hx.2⟩
  · intro a b hab c d hcd x hne hx hy
    exact hdisjoint a b hab c d hcd x hne
      ⟨(P a b hab).support_toPath_subset_support hx.1, hx.2⟩
      ⟨(P c d hcd).support_toPath_subset_support hy.1, hy.2⟩

private theorem l34Reverse_neighbor_unique {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {a r b c : V} (hdeg : H.degree a ≤ 2)
    (hr : H.Adj a r) (hb : H.Adj a b) (hc : H.Adj a c)
    (hbr : b ≠ r) (hcr : c ≠ r) : b = c := by
  by_contra hbc
  have hsub : ({r, b, c} : Finset V) ⊆ H.neighborFinset a := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> simp_all
  have hcard := Finset.card_le_card hsub
  have hthree : ({r, b, c} : Finset V).card = 3 := by
    simp [hbc, Ne.symm hbr, Ne.symm hcr]
  rw [hthree, SimpleGraph.card_neighborFinset_eq_degree] at hcard
  omega

private theorem l34Reverse_linear_paths {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {a b c r : V} (hra : H.Adj r a)
    (p : H.Walk a b) (q : H.Walk a c)
    (hp : (p.cons hra).IsPath) (hq : (q.cons hra).IsPath)
    (hdeg : ∀ x ∈ p.support, H.degree x ≤ 2) :
    p.support <+: q.support ∨ q.support <+: p.support := by
  induction p generalizing c r with
  | nil =>
    left
    cases q <;> simp
  | @cons a b d hab p ih =>
    cases q with
    | nil =>
      right
      simp
    | @cons _ c e hac q =>
      have hbc : b = c := l34Reverse_neighbor_unique H
        (hdeg a (by simp)) hra.symm hab hac
        (by
          intro h
          have hnot := (SimpleGraph.Walk.cons_isPath_iff hra (p.cons hab)).mp hp |>.2
          exact hnot (List.mem_cons_of_mem a (h ▸ p.start_mem_support)))
        (by
          intro h
          have hnot := (SimpleGraph.Walk.cons_isPath_iff hra (q.cons hac)).mp hq |>.2
          exact hnot (List.mem_cons_of_mem a (h ▸ q.start_mem_support)))
      subst c
      have h := ih hab q hp.of_cons hq.of_cons (fun x hx => hdeg x (by simp [hx]))
      simpa only [SimpleGraph.Walk.support_cons, List.cons_prefix_cons, true_and] using h

private theorem l34Reverse_rooted_prefix {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (r : V)
    (hdeg : ∀ x, x ≠ r → H.Reachable r x → H.degree x ≤ 2)
    {a b : V} (p : H.Walk r a) (q : H.Walk r b)
    (hp : p.IsPath) (hq : q.IsPath) (hsnd : p.snd = q.snd) :
    p.support <+: q.support ∨ q.support <+: p.support := by
  cases p with
  | nil =>
    left
    cases q <;> simp
  | @cons _ u a hru p =>
    cases q with
    | nil =>
      right
      simp
    | @cons _ v b hrv q =>
      have huv : u = v := by simpa only [SimpleGraph.Walk.snd_cons] using hsnd
      subst v
      have h := l34Reverse_linear_paths H hru p q hp hq (fun x hx =>
        hdeg x (fun h => ((SimpleGraph.Walk.cons_isPath_iff hru p).mp hp).2
          (h ▸ hx)) ((p.cons hru).takeUntil x (List.mem_cons_of_mem r hx)).reachable)
      simpa only [SimpleGraph.Walk.support_cons, List.cons_prefix_cons, true_and] using h

private theorem l34Reverse_maximal_arm {V : Type} [Fintype V]
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

private theorem l34Reverse_arms_meet {V : Type} [DecidableEq V]
    {H : SimpleGraph V} (ha : H.IsAcyclic) {r a b x : V}
    (p : H.Walk r a) (q : H.Walk r b) (hp : p.IsPath) (hq : q.IsPath)
    (hsnd : p.snd ≠ q.snd) (hxp : x ∈ p.support) (hxq : x ∈ q.support) : x = r := by
  by_contra hxr
  have heq := (ha.subsingleton_path r x).elim
    (⟨p.takeUntil x hxp, hp.takeUntil hxp⟩ : H.Path r x)
    ⟨q.takeUntil x hxq, hq.takeUntil hxq⟩
  have hs := congrArg (fun z : H.Path r x => z.val.snd) heq
  rw [SimpleGraph.Walk.snd_takeUntil hxr p hxp,
    SimpleGraph.Walk.snd_takeUntil hxr q hxq] at hs
  exact hsnd hs

private theorem l34Reverse_prefix_end {V : Type} {H : SimpleGraph V} {r a b : V}
    (p : H.Walk r a) (q : H.Walk r b) (h : p.support <+: q.support)
    (hlen : p.length = q.length) : a = b := by
  have hs : p.support = q.support := h.eq_of_length (by simp [hlen])
  have he := congrArg List.getLast? hs
  rw [List.getLast?_eq_some_getLast p.support_ne_nil,
    List.getLast?_eq_some_getLast q.support_ne_nil,
    SimpleGraph.Walk.getLast_support, SimpleGraph.Walk.getLast_support] at he
  exact Option.some.inj he

private structure l34ReverseArmData {V : Type} (H : SimpleGraph V) (r u : V) where
  finish : V
  walk : H.Walk r finish
  isPath : walk.IsPath
  snd_eq : walk.snd = u
  maximal : ∀ t, ∀ p : H.Walk r t, p.IsPath → p.snd = u → p.length ≤ walk.length

private def l34ReverseArm {V : Type} [Fintype V] (H : SimpleGraph V)
    {r u : V} (hru : H.Adj r u) : l34ReverseArmData H r u :=
  Classical.choice (by
    obtain ⟨t, p, hp, hsnd, hmax⟩ := l34Reverse_maximal_arm H hru
    exact ⟨⟨t, p, hp, hsnd, hmax⟩⟩)

private def l34ReversePath {V : Type} [DecidableEq V] {H : SimpleGraph V}
    {r x : V} (hr : H.Reachable r x) : H.Path r x := hr.some.toPath

private def l34ReversePlace {V W : Type} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {G : SimpleGraph W}
    (φ : V ↪ W) (P : ∀ a b, H.Adj a b → G.Walk (φ a) (φ b))
    {r x : V} (hr : H.Reachable r x) : W :=
  if hx : x = r then φ x else
    let p := l34ReversePath hr
    let hne : ¬ p.val.Nil := fun h => hx (p.isPath.nil_iff_eq.mp h).symm
    let arm := l34ReverseArm H (p.val.adj_snd hne)
    (l34Expand φ P arm.walk).getVert p.val.length

private theorem l34ReversePlace_root {V W : Type} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {G : SimpleGraph W}
    (φ : V ↪ W) (P : ∀ a b, H.Adj a b → G.Walk (φ a) (φ b)) (r : V)
    (hr : H.Reachable r r) : l34ReversePlace φ P hr = φ r := by
  simp only [l34ReversePlace, dite_true]

private theorem l34ReversePlace_on_arm {V W : Type} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {G : SimpleGraph W}
    (φ : V ↪ W) (P : ∀ a b, H.Adj a b → G.Walk (φ a) (φ b))
    (ha : H.IsAcyclic) {r x u : V} (hr : H.Reachable r x)
    (p : H.Walk r x) (hp : p.IsPath) (hx : x ≠ r)
    (hru : H.Adj r u) (hsnd : p.snd = u) :
    l34ReversePlace φ P hr =
      (l34Expand φ P (l34ReverseArm H hru).walk).getVert p.length := by
  have heq : (l34ReversePath hr).val = p :=
    l34Structure_paths_unique ha (l34ReversePath hr).isPath hp
  cases heq
  subst u
  simp only [l34ReversePlace, hx, dite_false]

private theorem l34ReversePlace_ne_root {V W : Type} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {G : SimpleGraph W}
    (φ : V ↪ W) (P : ∀ a b, H.Adj a b → G.Walk (φ a) (φ b))
    (ha : H.IsAcyclic)
    (hpath : ∀ a b (h : H.Adj a b), (P a b h).IsPath)
    (havoid : ∀ a b (h : H.Adj a b) z, z ∈ WalkInterior (P a b h) → z ∉ Set.range φ)
    (hdisjoint : ∀ a b (hab : H.Adj a b) c d (hcd : H.Adj c d) z,
      ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) →
      z ∈ WalkInterior (P a b hab) → z ∈ WalkInterior (P c d hcd) → False)
    {r x : V} (hr : H.Reachable r x) (hx : x ≠ r) :
    l34ReversePlace φ P hr ≠ φ r := by
  let p := l34ReversePath hr
  have hn : ¬p.val.Nil := fun h => hx (p.isPath.nil_iff_eq.mp h).symm
  let arm := l34ReverseArm H (p.val.adj_snd hn)
  rw [l34ReversePlace_on_arm φ P ha hr p.val p.isPath hx (p.val.adj_snd hn) rfl]
  have hlen := (arm.maximal x p.val p.isPath rfl).trans
    (l34ExpandLength φ P arm.walk)
  intro heq
  have hpaths := l34ExpandPath φ P hpath havoid hdisjoint arm.walk arm.isPath
  have hz := (hpaths.getVert_eq_start_iff hlen).mp heq
  exact hn (SimpleGraph.Walk.length_eq_zero_iff.mp hz)

private theorem l34ReversePlace_support {V W : Type} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {G : SimpleGraph W}
    (φ : V ↪ W) (P : ∀ a b, H.Adj a b → G.Walk (φ a) (φ b))
    {r x : V} (hr : H.Reachable r x) :
    ∃ t, ∃ p : H.Walk r t, l34ReversePlace φ P hr ∈ (l34Expand φ P p).support := by
  by_cases hx : x = r
  · subst x
    exact ⟨r, .nil, by simp [l34ReversePlace_root, l34Expand]⟩
  · let p := l34ReversePath hr
    have hn : ¬p.val.Nil := fun h => hx (p.isPath.nil_iff_eq.mp h).symm
    let arm := l34ReverseArm H (p.val.adj_snd hn)
    refine ⟨arm.finish, arm.walk, ?_⟩
    simpa only [l34ReversePlace, hx, dite_false] using
      (l34Expand φ P arm.walk).getVert_mem_support p.val.length

private theorem l34ExpandReachable {V W : Type} [DecidableEq V]
    {H : SimpleGraph V} {G : SimpleGraph W}
    (φ : V ↪ W) (P : ∀ a b, H.Adj a b → G.Walk (φ a) (φ b))
    (havoid : ∀ a b (h : H.Adj a b) z, z ∈ WalkInterior (P a b h) → z ∉ Set.range φ)
    (hdisjoint : ∀ a b (hab : H.Adj a b) c d (hcd : H.Adj c d) z,
      ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) →
      z ∈ WalkInterior (P a b hab) → z ∈ WalkInterior (P c d hcd) → False)
    {a b c d : V} (p : H.Walk a b) (q : H.Walk c d) {z : W}
    (hp : z ∈ (l34Expand φ P p).support) (hq : z ∈ (l34Expand φ P q).support) :
    H.Reachable a c := by
  have hcommon {u : V} (hu : u ∈ p.support) (hu' : u ∈ q.support) :
      H.Reachable a c :=
    (p.takeUntil u hu).reachable.trans (q.takeUntil u hu').reachable.symm
  rcases l34ExpandSupport φ P p hp with ⟨u, hu, rfl⟩ | ⟨u, v, huv, he, hz⟩
  · exact hcommon hu (l34ExpandRange φ P havoid q hq)
  rcases l34ExpandSupport φ P q hq with ⟨u', _, heq⟩ | ⟨u', v', huv', he', hz'⟩
  · exact (havoid u v huv z hz ⟨u', heq.symm⟩).elim
  by_cases hsame : (u = u' ∧ v = v') ∨ (u = v' ∧ v = u')
  · rcases hsame with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hcommon (p.fst_mem_support_of_mem_edges he)
        (q.fst_mem_support_of_mem_edges he')
    · exact hcommon (p.fst_mem_support_of_mem_edges he)
        (q.snd_mem_support_of_mem_edges he')
  · exact (hdisjoint u v huv u' v' huv' z hsame hz hz').elim

open scoped Classical in
private theorem l34ReversePlace_injective {V W : Type} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {G : SimpleGraph W}
    (φ : V ↪ W) (P : ∀ a b, H.Adj a b → G.Walk (φ a) (φ b))
    (ha : H.IsAcyclic)
    (hpath : ∀ a b (h : H.Adj a b), (P a b h).IsPath)
    (havoid : ∀ a b (h : H.Adj a b) z, z ∈ WalkInterior (P a b h) → z ∉ Set.range φ)
    (hdisjoint : ∀ a b (hab : H.Adj a b) c d (hcd : H.Adj c d) z,
      ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) →
      z ∈ WalkInterior (P a b hab) → z ∈ WalkInterior (P c d hcd) → False)
    {r x y : V} (hdeg : ∀ z, z ≠ r → H.Reachable r z → H.degree z ≤ 2)
    (hrx : H.Reachable r x) (hry : H.Reachable r y)
    (heq : l34ReversePlace φ P hrx = l34ReversePlace φ P hry) : x = y := by
  classical
  by_cases hx : x = r
  · subst x
    by_contra hy
    exact l34ReversePlace_ne_root φ P ha hpath havoid hdisjoint hry (Ne.symm hy)
      (heq.symm.trans (l34ReversePlace_root φ P r hrx))
  by_cases hy : y = r
  · subst y
    exact (l34ReversePlace_ne_root φ P ha hpath havoid hdisjoint hrx hx
      (heq.trans (l34ReversePlace_root φ P r hry))).elim
  let p := l34ReversePath hrx
  let q := l34ReversePath hry
  have hpn : ¬p.val.Nil := fun h => hx (p.isPath.nil_iff_eq.mp h).symm
  have hqn : ¬q.val.Nil := fun h => hy (q.isPath.nil_iff_eq.mp h).symm
  let arm := l34ReverseArm H (p.val.adj_snd hpn)
  have hpx := l34ReversePlace_on_arm φ P ha hrx p.val p.isPath hx
    (p.val.adj_snd hpn) rfl
  by_cases hsnd : p.val.snd = q.val.snd
  · have hqy := l34ReversePlace_on_arm φ P ha hry q.val q.isPath hy
      (p.val.adj_snd hpn) hsnd.symm
    rw [hpx, hqy] at heq
    have hpaths := l34ExpandPath φ P hpath havoid hdisjoint arm.walk arm.isPath
    have hlen := hpaths.getVert_injOn
        ((arm.maximal x p.val p.isPath rfl).trans (l34ExpandLength φ P arm.walk))
        ((arm.maximal y q.val q.isPath hsnd.symm).trans (l34ExpandLength φ P arm.walk))
        heq
    rcases l34Reverse_rooted_prefix H r hdeg p.val q.val p.isPath q.isPath hsnd with hpq | hqp
    · exact l34Reverse_prefix_end p.val q.val hpq hlen
    · exact (l34Reverse_prefix_end q.val p.val hqp hlen.symm).symm
  · let arm' := l34ReverseArm H (q.val.adj_snd hqn)
    have hqy := l34ReversePlace_on_arm φ P ha hry q.val q.isPath hy
      (q.val.adj_snd hqn) rfl
    have hmeet : l34ReversePlace φ P hrx = φ r := by
      apply l34ExpandMeet φ P havoid hdisjoint arm.walk arm'.walk r
      · intro z hz hz'
        exact l34Reverse_arms_meet ha arm.walk arm'.walk arm.isPath arm'.isPath
          (by simpa only [arm.snd_eq, arm'.snd_eq] using hsnd) hz hz'
      · rw [hpx]
        exact (l34Expand φ P arm.walk).getVert_mem_support _
      · rw [heq, hqy]
        exact (l34Expand φ P arm'.walk).getVert_mem_support _
    exact (l34ReversePlace_ne_root φ P ha hpath havoid hdisjoint hrx hx hmeet).elim

private theorem l34ReversePlace_adj {V W : Type} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {G : SimpleGraph W}
    (φ : V ↪ W) (P : ∀ a b, H.Adj a b → G.Walk (φ a) (φ b))
    (ha : H.IsAcyclic) {r x y : V}
    (hrx : H.Reachable r x) (hry : H.Reachable r y) (hxy : H.Adj x y) :
    G.Adj (l34ReversePlace φ P hrx) (l34ReversePlace φ P hry) := by
  have hstep {a b : V} (hra : H.Reachable r a) (hrb : H.Reachable r b)
      (p : H.Walk r a) (hp : p.IsPath) (hab : H.Adj a b)
      (hq : (p.concat hab).IsPath) :
      G.Adj (l34ReversePlace φ P hra) (l34ReversePlace φ P hrb) := by
    let q := p.concat hab
    have hb : b ≠ r := by
      intro heq
      subst b
      have hz := congrArg SimpleGraph.Walk.length (l34Structure_closed_path_eq_nil hq)
      simp only [SimpleGraph.Walk.length_concat, SimpleGraph.Walk.length_nil] at hz
      omega
    have hqn : ¬q.Nil := fun h => hb (hq.nil_iff_eq.mp h).symm
    let arm := l34ReverseArm H (q.adj_snd hqn)
    have hbplace := l34ReversePlace_on_arm φ P ha hrb q hq hb (q.adj_snd hqn) rfl
    have haplace : l34ReversePlace φ P hra = (l34Expand φ P arm.walk).getVert p.length := by
      by_cases hax : a = r
      · subst a
        rw [l34Structure_closed_path_eq_nil hp]
        simpa only [SimpleGraph.Walk.length_nil, SimpleGraph.Walk.getVert_zero] using
          l34ReversePlace_root φ P r hra
      · exact l34ReversePlace_on_arm φ P ha hra p hp hax (q.adj_snd hqn)
          (l34Structure_snd_concat p hab hax).symm
    rw [haplace, hbplace]
    have hlen := (arm.maximal b q hq rfl).trans (l34ExpandLength φ P arm.walk)
    simp only [q, SimpleGraph.Walk.length_concat]
    exact (l34Expand φ P arm.walk).adj_getVert_succ
      (Nat.lt_of_succ_le (by simpa only [q, SimpleGraph.Walk.length_concat] using hlen))
  let p := l34ReversePath hrx
  let q := l34ReversePath hry
  rcases l34Structure_adj_paths ha p.isPath q.isPath hxy with hpq | hqp
  · apply hstep hrx hry p.val p.isPath hxy
    rw [← hpq]
    exact q.isPath
  · exact (hstep hry hrx q.val q.isPath hxy.symm (hqp ▸ p.isPath)).symm

private theorem l34ReversePlace_root_congr {V W : Type} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {G : SimpleGraph W}
    (φ : V ↪ W) (P : ∀ a b, H.Adj a b → G.Walk (φ a) (φ b))
    {r s x : V} (hr : H.Reachable r x) (hs : H.Reachable s x) (heq : r = s) :
    l34ReversePlace φ P hr = l34ReversePlace φ P hs := by
  subst s
  rfl

private theorem l34TopologicalSubgraph {V W : Type} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {G : SimpleGraph W}
    (hbeta : beta H = 0) (htop : ContainsTopologicalMinor H G) : ContainsSubgraph H G := by
  classical
  obtain ⟨φ, P, hpath, havoid, hdisjoint⟩ := l34SimpleModel htop
  have ha := l34Structure_acyclic H hbeta
  let f (x : V) := l34ReversePlace φ P (l34Structure_root_reachable H x)
  have hdeg (x z : V) (hz : z ≠ l34Structure_root H x)
      (hrz : H.Reachable (l34Structure_root H x) z) : H.degree z ≤ 2 := by
    have heq := l34Structure_root_eq H ((l34Structure_root_reachable H x).symm.trans hrz)
    exact l34Structure_degree_le_two H hbeta (by rwa [← heq])
  refine ⟨⟨f, ?_⟩, ?_⟩
  · intro x y heq
    obtain ⟨a, p, hp⟩ := l34ReversePlace_support φ P (l34Structure_root_reachable H x)
    obtain ⟨b, q, hq⟩ := l34ReversePlace_support φ P (l34Structure_root_reachable H y)
    change f x ∈ _ at hp
    change f y ∈ _ at hq
    have hr := l34ExpandReachable φ P havoid hdisjoint p q hp (heq.symm ▸ hq)
    have hroots := l34Structure_root_eq H
      ((l34Structure_root_reachable H x).symm.trans (hr.trans (l34Structure_root_reachable H y)))
    let hrx : H.Reachable (l34Structure_root H y) x :=
      hroots ▸ l34Structure_root_reachable H x
    have hplace := l34ReversePlace_root_congr φ P (l34Structure_root_reachable H x) hrx hroots
    exact l34ReversePlace_injective φ P ha hpath havoid hdisjoint (hdeg y) _ _
      (hplace.symm.trans heq)
  · intro x y hxy
    change G.Adj (l34ReversePlace φ P _) (l34ReversePlace φ P _)
    have hroots := l34Structure_root_eq H hxy.reachable
    let hrx : H.Reachable (l34Structure_root H y) x :=
      hroots ▸ l34Structure_root_reachable H x
    rw [l34ReversePlace_root_congr φ P (l34Structure_root_reachable H x) hrx hroots]
    exact l34ReversePlace_adj φ P ha _ _ hxy

private theorem l34SubgraphTopological {V W : Type} {H : SimpleGraph V}
    {G : SimpleGraph W} (h : ContainsSubgraph H G) : ContainsTopologicalMinor H G := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ, fun _ _ hab => .cons (hφ hab) .nil, ?_, ?_⟩
  · intro a b hab x hx
    simp [WalkInterior] at hx
    exact (hx.1.elim hx.2.1 hx.2.2).elim
  · intro a b hab c d hcd x _ hx _
    simp [WalkInterior] at hx
    exact hx.1.elim hx.2.1 hx.2.2

private abbrev l34ForwardEdge {m : ℕ} (H : SimpleGraph (Fin m)) :=
  {e : Fin m × Fin m // e.1 < e.2 ∧ H.Adj e.1 e.2}

private abbrev l34ForwardVertex {m : ℕ} (H : SimpleGraph (Fin m)) :=
  Fin m ⊕ (l34ForwardEdge H × Fin (m + 1))

private def l34ForwardGraph {m : ℕ} (H : SimpleGraph (Fin m)) :
    SimpleGraph (l34ForwardVertex H) where
  Adj x y := match x, y with
    | .inl a, .inr (e, k) =>
        (a = e.1.1 ∧ k.val = 0) ∨ (a = e.1.2 ∧ k.val = m)
    | .inr (e, k), .inl a =>
        (a = e.1.1 ∧ k.val = 0) ∨ (a = e.1.2 ∧ k.val = m)
    | .inr (e, k), .inr (f, l) =>
        e = f ∧ (k.val + 1 = l.val ∨ l.val + 1 = k.val)
    | .inl _, .inl _ => False
  symm := ⟨by
    rintro (a | ⟨e, k⟩) (b | ⟨f, l⟩) h
    · exact h
    · exact h
    · exact h
    · exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by
    rintro (a | ⟨e, k⟩) h
    · exact h
    · rcases h.2 with h | h <;> omega⟩

private theorem l34ForwardAdjFirst {m : ℕ} (H : SimpleGraph (Fin m))
    (e : l34ForwardEdge H) :
    (l34ForwardGraph H).Adj (.inl e.1.1) (.inr (e, ⟨0, Nat.zero_lt_succ m⟩)) :=
  Or.inl ⟨rfl, rfl⟩

private theorem l34ForwardAdjLast {m : ℕ} (H : SimpleGraph (Fin m))
    (e : l34ForwardEdge H) (k : Fin (m + 1)) (hk : k.val = m) :
    (l34ForwardGraph H).Adj (.inr (e, k)) (.inl e.1.2) :=
  Or.inr ⟨rfl, hk⟩

private theorem l34ForwardAdjStep {m : ℕ} (H : SimpleGraph (Fin m))
    (e : l34ForwardEdge H) (k l : Fin (m + 1)) (hkl : k.val + 1 = l.val) :
    (l34ForwardGraph H).Adj (.inr (e, k)) (.inr (e, l)) :=
  ⟨rfl, Or.inl hkl⟩

private def l34ForwardTail {m : ℕ} (H : SimpleGraph (Fin m))
    (e : l34ForwardEdge H) (k : ℕ) (hk : k ≤ m) :
    (l34ForwardGraph H).Walk (.inr (e, ⟨k, by omega⟩)) (.inl e.1.2) :=
  if h : k < m then
    .cons (l34ForwardAdjStep H e ⟨k, by omega⟩ ⟨k + 1, by omega⟩ rfl)
      (l34ForwardTail H e (k + 1) (by omega))
  else
    .cons (l34ForwardAdjLast H e ⟨k, Nat.lt_succ_of_le hk⟩
      (show k = m from Nat.le_antisymm hk (Nat.le_of_not_gt h))) .nil
termination_by m - k

private theorem l34ForwardTailSupport {m : ℕ} (H : SimpleGraph (Fin m))
    (e : l34ForwardEdge H) (k : ℕ) (hk : k ≤ m) (x : l34ForwardVertex H)
    (hx : x ∈ (l34ForwardTail H e k hk).support) :
    x = .inl e.1.2 ∨ ∃ i, x = .inr (e, i) := by
  rw [l34ForwardTail] at hx
  split at hx
  · simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Or.inr ⟨_, rfl⟩
    · exact l34ForwardTailSupport H e (k + 1) (by omega) x hx
  · simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl rfl
termination_by m - k

private def l34ForwardWalk {m : ℕ} (H : SimpleGraph (Fin m))
    (a b : Fin m) (hab : H.Adj a b) :
    (l34ForwardGraph H).Walk (.inl a) (.inl b) :=
  if h : a < b then
    .cons (l34ForwardAdjFirst H ⟨(a, b), h, hab⟩)
      (l34ForwardTail H ⟨(a, b), h, hab⟩ 0 (Nat.zero_le m))
  else
    (SimpleGraph.Walk.cons
      (l34ForwardAdjFirst H
        ⟨(b, a), lt_of_le_of_ne (le_of_not_gt h) hab.ne.symm, hab.symm⟩)
      (l34ForwardTail H ⟨(b, a), lt_of_le_of_ne (le_of_not_gt h) hab.ne.symm, hab.symm⟩
        0 (Nat.zero_le m))).reverse

private theorem l34ForwardWalkInterior {m : ℕ} (H : SimpleGraph (Fin m))
    (a b : Fin m) (hab : H.Adj a b) (x : l34ForwardVertex H)
    (hx : x ∈ WalkInterior (l34ForwardWalk H a b hab)) :
    ∃ (e : l34ForwardEdge H) (i : Fin (m + 1)), x = .inr (e, i) ∧
      ((a = e.1.1 ∧ b = e.1.2) ∨ (a = e.1.2 ∧ b = e.1.1)) := by
  obtain ⟨hx, hxa, hxb⟩ := hx
  unfold l34ForwardWalk at hx
  split at hx
  · simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
    rcases hx with hx | hx
    · exact (hxa hx).elim
    · rcases l34ForwardTailSupport H _ 0 (Nat.zero_le m) x hx with hx | ⟨i, hx⟩
      · exact (hxb hx).elim
      · exact ⟨_, i, hx, Or.inl ⟨rfl, rfl⟩⟩
  · simp only [SimpleGraph.Walk.support_reverse, List.mem_reverse,
      SimpleGraph.Walk.support_cons, List.mem_cons] at hx
    rcases hx with hx | hx
    · exact (hxb hx).elim
    · rcases l34ForwardTailSupport H _ 0 (Nat.zero_le m) x hx with hx | ⟨i, hx⟩
      · exact (hxa hx).elim
      · exact ⟨_, i, hx, Or.inr ⟨rfl, rfl⟩⟩

private theorem l34ForwardTopological {m : ℕ} (H : SimpleGraph (Fin m)) :
    ContainsTopologicalMinor H (l34ForwardGraph H) := by
  refine ⟨⟨Sum.inl, Sum.inl_injective⟩, l34ForwardWalk H, ?_, ?_⟩
  · intro a b hab x hx ⟨y, hy⟩
    obtain ⟨e, i, hx, _⟩ := l34ForwardWalkInterior H a b hab x hx
    cases hy.trans hx
  · intro a b hab c d hcd x hne hx hy
    obtain ⟨e, i, rfl, he⟩ := l34ForwardWalkInterior H a b hab x hx
    obtain ⟨f, j, hf, hj⟩ := l34ForwardWalkInterior H c d hcd _ hy
    have hef : e = f := congrArg Prod.fst (Sum.inr.inj hf)
    subst f
    exact hne (by rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp)

private theorem l34ForwardMissing {m : ℕ} (H : SimpleGraph (Fin m))
    (ψ : Fin m ↪ l34ForwardVertex H) (e : l34ForwardEdge H) :
    ∃ k : Fin (m + 1), Sum.inr (e, k) ∉ Set.range ψ := by
  classical
  by_contra hn
  have hex : ∀ k : Fin (m + 1), ∃ x, ψ x = Sum.inr (e, k) := by
    simpa only [not_exists, not_not, Set.mem_range, not_forall] using hn
  let f : Fin (m + 1) → Fin m := fun k => (hex k).choose
  have hf (k : Fin (m + 1)) : ψ (f k) = Sum.inr (e, k) := (hex k).choose_spec
  have hinj : Function.Injective f := by
    intro k l hkl
    have heq := (hf k).symm.trans ((congrArg ψ hkl).trans (hf l))
    exact congrArg Prod.snd (Sum.inr.inj heq)
  have hc := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin] at hc
  omega

private def l34ForwardOwner {m : ℕ} {H : SimpleGraph (Fin m)}
    (cut : l34ForwardEdge H → Fin (m + 1)) : l34ForwardVertex H → Fin m
  | .inl a => a
  | .inr (e, k) => if k < cut e then e.1.1 else e.1.2

private def l34ForwardRank {m : ℕ} {H : SimpleGraph (Fin m)}
    (cut : l34ForwardEdge H → Fin (m + 1)) : l34ForwardVertex H → ℕ
  | .inl _ => 0
  | .inr (e, k) => if k < cut e then k.val + 1 else m + 1 - k.val

private theorem l34ForwardOwnerAdj {m : ℕ} (H : SimpleGraph (Fin m))
    (cut : l34ForwardEdge H → Fin (m + 1))
    (x y : l34ForwardVertex H)
    (hx : ∀ e, x ≠ Sum.inr (e, cut e)) (hy : ∀ e, y ≠ Sum.inr (e, cut e))
    (hxy : (l34ForwardGraph H).Adj x y) :
    l34ForwardOwner cut x = l34ForwardOwner cut y := by
  rcases x with a | ⟨e, k⟩ <;> rcases y with b | ⟨f, l⟩
  · exact hxy.elim
  · have hne : l ≠ cut f := fun h => hy f (by simp [h])
    rcases hxy with ⟨rfl, hl⟩ | ⟨rfl, hl⟩
    · have hh : l < cut f := by have := Fin.isLt (cut f); omega
      simp only [l34ForwardOwner, hh, ite_true]
    · have hh : ¬l < cut f := by have := Fin.isLt (cut f); omega
      simp only [l34ForwardOwner, hh, ite_false]
  · have hne : k ≠ cut e := fun h => hx e (by simp [h])
    rcases hxy with ⟨rfl, hk⟩ | ⟨rfl, hk⟩
    · have hh : k < cut e := by have := Fin.isLt (cut e); omega
      simp only [l34ForwardOwner, hh, ite_true]
    · have hh : ¬k < cut e := by have := Fin.isLt (cut e); omega
      simp only [l34ForwardOwner, hh, ite_false]
  · obtain ⟨rfl, hkl⟩ := hxy
    have hk : k ≠ cut e := fun h => hx e (by simp [h])
    have hl : l ≠ cut e := fun h => hy e (by simp [h])
    have hh : (k < cut e) ↔ (l < cut e) := by
      rcases hkl with h | h <;> constructor <;> intro hh <;> omega
    simp only [l34ForwardOwner, hh]

private theorem l34ForwardRankAdj {m : ℕ} (H : SimpleGraph (Fin m))
    (cut : l34ForwardEdge H → Fin (m + 1))
    (x y : l34ForwardVertex H)
    (hx : ∀ e, x ≠ Sum.inr (e, cut e)) (hy : ∀ e, y ≠ Sum.inr (e, cut e))
    (hxy : (l34ForwardGraph H).Adj x y) :
    l34ForwardRank cut x ≠ l34ForwardRank cut y := by
  rcases x with a | ⟨e, k⟩ <;> rcases y with b | ⟨f, l⟩
  · exact hxy.elim
  · simp only [l34ForwardRank]
    have := l.isLt
    split <;> omega
  · simp only [l34ForwardRank]
    have := k.isLt
    split <;> omega
  · obtain ⟨rfl, hkl⟩ := hxy
    have hk : k ≠ cut e := fun h => hx e (by simp [h])
    have hl : l ≠ cut e := fun h => hy e (by simp [h])
    simp only [l34ForwardRank]
    split <;> split <;> rcases hkl with h | h <;> omega

private theorem l34ForwardLowerUnique {m : ℕ} (H : SimpleGraph (Fin m))
    (cut : l34ForwardEdge H → Fin (m + 1))
    (x y z : l34ForwardVertex H) (hx : ∀ e, x ≠ Sum.inr (e, cut e))
    (hya : ∀ e, y ≠ Sum.inr (e, cut e)) (hza : ∀ e, z ≠ Sum.inr (e, cut e))
    (hxy : (l34ForwardGraph H).Adj x y) (hxz : (l34ForwardGraph H).Adj x z)
    (hy : l34ForwardRank cut y < l34ForwardRank cut x)
    (hz : l34ForwardRank cut z < l34ForwardRank cut x) : y = z := by
  rcases x with a | ⟨e, k⟩
  · simp only [l34ForwardRank] at hy
    omega
  have hk : k ≠ cut e := fun h => hx e (by simp [h])
  have hm := e.1.1.isLt
  rcases y with a | ⟨f, l⟩ <;> rcases z with b | ⟨g, j⟩
  · rcases hxy with ⟨rfl, ha⟩ | ⟨rfl, ha⟩ <;>
      rcases hxz with ⟨rfl, hb⟩ | ⟨rfl, hb⟩
    · rfl
    · omega
    · omega
    · rfl
  · obtain ⟨rfl, hkj⟩ := hxz
    have hjne : j ≠ cut e := fun h => hza e (by simp [h])
    simp only [l34ForwardRank] at hy hz
    rcases hxy with ⟨rfl, ha⟩ | ⟨rfl, ha⟩
    all_goals
      have hj := j.isLt
      split_ifs at hy hz <;> rcases hkj with h | h <;> omega
  · obtain ⟨rfl, hkl⟩ := hxy
    have hlne : l ≠ cut e := fun h => hya e (by simp [h])
    simp only [l34ForwardRank] at hy hz
    rcases hxz with ⟨rfl, ha⟩ | ⟨rfl, ha⟩
    all_goals
      have hl := l.isLt
      split_ifs at hy hz <;> rcases hkl with h | h <;> omega
  · obtain ⟨rfl, hkl⟩ := hxy
    obtain ⟨rfl, hkj⟩ := hxz
    have hlne : l ≠ cut e := fun h => hya e (by simp [h])
    have hjne : j ≠ cut e := fun h => hza e (by simp [h])
    have hl := l.isLt
    have hj := j.isLt
    suffices hlj : l = j by simp [hlj]
    apply Fin.ext
    simp only [l34ForwardRank] at hy hz
    split_ifs at hy hz <;> rcases hkl with h | h <;> rcases hkj with h' | h' <;> omega

private theorem l34ForwardAcyclicRank {V : Type} (G : SimpleGraph V) (rank : V → ℕ)
    (hne : ∀ x y, G.Adj x y → rank x ≠ rank y)
    (hunique : ∀ x y z, G.Adj x y → G.Adj x z → rank y < rank x →
      rank z < rank x → y = z) : G.IsAcyclic := by
  classical
  intro u p hp
  obtain ⟨v, hv, hmax⟩ := p.support.toFinset.exists_max_image rank
    ⟨u, by simp⟩
  have hv' : v ∈ p.support := by simpa using hv
  let q := p.rotate v hv'
  have hq : q.IsCycle := hp.rotate hv'
  have hs := q.adj_snd hq.not_nil
  have ht := q.adj_penultimate hq.not_nil
  have hsupp : q.snd ∈ p.support := by
    rw [← p.mem_support_rotate_iff v hv']
    exact q.getVert_mem_support 1
  have htupp : q.penultimate ∈ p.support := by
    rw [← p.mem_support_rotate_iff v hv']
    exact q.getVert_mem_support (q.length - 1)
  have hsle := hmax q.snd (by simpa using hsupp)
  have htle := hmax q.penultimate (by simpa using htupp)
  exact hq.snd_ne_penultimate (hunique v q.snd q.penultimate hs ht.symm
    (lt_of_le_of_ne hsle (hne v q.snd hs).symm)
    (lt_of_le_of_ne htle (hne v q.penultimate ht.symm).symm))

open scoped Classical in
private theorem l34ForwardHigh {m : ℕ} (H : SimpleGraph (Fin m))
    (ψ : Fin m ↪ l34ForwardVertex H)
    (hψ : ∀ ⦃a b⦄, H.Adj a b → (l34ForwardGraph H).Adj (ψ a) (ψ b))
    {x : Fin m} (hx : 3 ≤ H.degree x) : ∃ a, ψ x = Sum.inl a := by
  classical
  cases hval : ψ x with
  | inl a => exact ⟨a, rfl⟩
  | inr p =>
    obtain ⟨e, k⟩ := p
    let pred : l34ForwardVertex H := if hk : k.val = 0 then .inl e.1.1
      else .inr (e, ⟨k.val - 1, by omega⟩)
    let succ : l34ForwardVertex H := if hk : k.val = m then .inl e.1.2
      else .inr (e, ⟨k.val + 1, by omega⟩)
    have hneighbors (y : l34ForwardVertex H)
        (hy : (l34ForwardGraph H).Adj (.inr (e, k)) y) : y = pred ∨ y = succ := by
      rcases y with a | ⟨f, l⟩
      · rcases hy with ⟨rfl, hk⟩ | ⟨rfl, hk⟩
        · exact .inl (by simp only [pred, hk, dite_true])
        · exact .inr (by simp only [succ, hk, dite_true])
      · obtain ⟨rfl, hkl⟩ := hy
        rcases hkl with hkl | hkl
        · right
          have hk : k.val ≠ m := by omega
          simp only [succ, hk, dite_false]
          exact congrArg Sum.inr (Prod.ext rfl (Fin.ext hkl.symm))
        · left
          have hk : k.val ≠ 0 := by omega
          simp only [pred, hk, dite_false]
          exact congrArg Sum.inr (Prod.ext rfl (Fin.ext (by
            change l.val = k.val - 1
            omega)))
    have hsub : (H.neighborFinset x).image ψ ⊆ {pred, succ} := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      have hadj := hψ ((H.mem_neighborFinset x z).mp hz)
      rw [hval] at hadj
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact hneighbors _ hadj
    have hcard := (Finset.card_le_card hsub).trans Finset.card_le_two
    rw [Finset.card_image_of_injective _ ψ.injective,
      SimpleGraph.card_neighborFinset_eq_degree] at hcard
    omega

/-- Lemma 3.4: `H`-topological-minor containment coincides with `H`-subgraph
containment on all finite graphs if and only if `β(H) = 0`. -/
theorem lemma34 {m : ℕ} (H : SimpleGraph (Fin m)) :
    (∀ (W : Type) [Fintype W] [DecidableEq W] (G : SimpleGraph W),
        ContainsTopologicalMinor H G ↔ ContainsSubgraph H G) ↔ beta H = 0 := by
  classical
  constructor
  · intro h
    obtain ⟨ψ, hψ⟩ := (h (l34ForwardVertex H) (l34ForwardGraph H)).mp
      (l34ForwardTopological H)
    let cut : l34ForwardEdge H → Fin (m + 1) :=
      fun e => (l34ForwardMissing H ψ e).choose
    have hcut (x : Fin m) (e : l34ForwardEdge H) : ψ x ≠ Sum.inr (e, cut e) :=
      fun heq => (l34ForwardMissing H ψ e).choose_spec ⟨x, heq⟩
    apply l34Structure_of_acyclic_branch_unique H
    · apply l34ForwardAcyclicRank H (fun x => l34ForwardRank cut (ψ x))
      · intro x y hxy
        exact l34ForwardRankAdj H cut _ _ (hcut x) (hcut y) (hψ hxy)
      · intro x y z hxy hxz hy hz
        exact ψ.injective (l34ForwardLowerUnique H cut _ _ _
          (hcut x) (hcut y) (hcut z) (hψ hxy) (hψ hxz) hy hz)
    · intro a b hab ha hb
      have howners : ∀ {x y}, H.Reachable x y →
          l34ForwardOwner cut (ψ x) = l34ForwardOwner cut (ψ y) := by
        intro x y ⟨p⟩
        induction p with
        | nil => rfl
        | @cons x y z hxy p ih =>
          exact (l34ForwardOwnerAdj H cut _ _ (hcut x) (hcut y) (hψ hxy)).trans ih
      have howner := howners hab
      obtain ⟨u, hu⟩ := l34ForwardHigh H ψ hψ ha
      obtain ⟨v, hv⟩ := l34ForwardHigh H ψ hψ hb
      rw [hu, hv] at howner
      exact ψ.injective (hu.trans ((congrArg Sum.inl howner).trans hv.symm))
  · intro hbeta W _ _ G
    constructor
    · intro htop
      exact l34TopologicalSubgraph hbeta htop
    · exact l34SubgraphTopological

end Qatlib.Papers.MinorClosed10.MainResults.Source
