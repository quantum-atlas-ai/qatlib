/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GraphConnect03.MainResults.Defs

/-!
# DFS trees and discovery-order reachability

This module defines the parent-chain relation `Descendant` and an undirected spanning `DFSTree`
with discovery-order and no-cross-edge conditions. It proves the corrected discovery-order
implication `lemma1_corrected`, converts between walks and reachability, and bounds
`dfsSearchCount` by twice the vertex count. See [DurrMhallaLei2003].

## Main statements

* `connected`: An undirected graph possessing a spanning `DFSTree` is connected.
* `lemma1_corrected`: Under the stated discovery-order condition on every vertex other than `u`
  reachable from `u` and able to reach a distinct `w`, reachability from `u` to `w` implies that
  `w` is a descendant of `u`.
* `dfsSearchCount_le`: The DFS search count for any visited subset is at most twice the total
  number of vertices.

## References

* [Durr et al., 2003][DurrMhallaLei2003]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace Qatlib.Papers.GraphConnect03.MainResults.UpperBounds

open Qatlib.Papers.GraphConnect03.MainResults.Defs

/-- The reflexive transitive closure of parent-to-child steps specified by the parent function. -/
def Descendant {n : ℕ} (parent : Vertex n → Option (Vertex n)) (u v : Vertex n) : Prop :=
  Relation.ReflTransGen (fun a b => parent b = some a) u v

namespace Descendant

variable {n : ℕ} {parent : Vertex n → Option (Vertex n)}

/-- Every vertex is its own descendant. -/
theorem refl (u : Vertex n) : Descendant parent u u :=
  Relation.ReflTransGen.refl

/-- The descendant relation is transitive. -/
theorem trans {a b c : Vertex n}
    (hab : Descendant parent a b) (hbc : Descendant parent b c) : Descendant parent a c :=
  Relation.ReflTransGen.trans hab hbc

/-- If the parent of `v` is `u`, then `v` is a descendant of `u`. -/
theorem step {u v : Vertex n} (h : parent v = some u) : Descendant parent u v :=
  Relation.ReflTransGen.single h

/-- Appending a parent-to-child step to a descendant chain preserves descendancy from the
starting vertex. -/
theorem of_tail {a b c : Vertex n} (hab : Descendant parent a b) (hbc : parent c = some b) :
    Descendant parent a c :=
  hab.tail hbc

end Descendant

/-- A rooted spanning parent structure for an undirected graph, with injective discovery times
increasing along tree edges and a no-cross-edge condition relating increasing-time graph
edges to descendancy. -/
structure DFSTree (n : ℕ) (G : UndirectedMatrix n) where

  parent : Vertex n → Option (Vertex n)

  disc : Vertex n → ℕ

  disc_injective : Function.Injective disc

  parent_edge : ∀ u p, parent u = some p → G.toDigraph.adj p u = true

  parent_disc : ∀ u p, parent u = some p → disc p < disc u

  root : Vertex n

  root_parent : parent root = none

  no_cross : ∀ u v : Vertex n, G.toDigraph.adj u v = true → disc u < disc v →
    Descendant parent u v

  spanning : ∀ v : Vertex n, Descendant parent root v

namespace DFSTree

variable {n : ℕ} {G : UndirectedMatrix n}

/-- Discovery time is nondecreasing along descendant chains in a DFS tree. -/
theorem desc_disc (T : DFSTree n G) {u v : Vertex n} (h : Descendant T.parent u v) :
    T.disc u ≤ T.disc v := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih => exact le_trans ih (le_of_lt (T.parent_disc _ _ hbc))

/-- If `c` is a proper descendant of `a` and has parent `b`, then `b` is also a descendant of
`a`. -/
theorem descendant_parent_of_tail (T : DFSTree n G) {a c b : Vertex n}
    (h : Descendant T.parent a c) (hp : T.parent c = some b) (hne : a ≠ c) :
    Descendant T.parent a b := by
  rcases Relation.ReflTransGen.cases_tail h with rfl | ⟨c', hc', hpc'⟩
  · exact absurd rfl hne
  · have hb : b = c' := Option.some.inj (hp.symm.trans hpc')
    rw [hb]
    exact hc'

/-- If `u` and `w` share a descendant and `u` has earlier discovery time than `w`, then `w` is a
descendant of `u`. -/
theorem descendant_of_descendant_of_disc_lt (T : DFSTree n G) {u w c : Vertex n}
    (huc : Descendant T.parent u c) (hwc : Descendant T.parent w c)
    (hlt : T.disc u < T.disc w) : Descendant T.parent u w := by
  revert hwc hlt
  induction huc with
  | refl =>
      intro hwc hlt
      have hle := T.desc_disc hwc
      omega
  | tail hab hbc ih =>
      rename_i b c
      intro hwc hlt
      by_cases hw : w = c
      · rw [hw]
        exact hab.tail hbc
      · exact ih (T.descendant_parent_of_tail hwc hbc hw) hlt

end DFSTree

/-- The existence of a directed graph walk of a specified natural length between two vertices. -/
def Walk {n : ℕ} (G : Digraph n) : ℕ → Vertex n → Vertex n → Prop
  | 0, s, t => s = t
  | m + 1, s, t => ∃ c : Vertex n, Walk G m s c ∧ G.adj c t = true

namespace Walk

/-- A walk of any finite length gives directed reachability. -/
theorem reach {n : ℕ} {G : Digraph n} {m : ℕ} {s t : Vertex n} (h : Walk G m s t) :
    G.Reach s t := by
  induction m generalizing t with
  | zero =>
      simp only [Walk] at h
      subst h
      exact Relation.ReflTransGen.refl
  | succ m ih =>
      simp only [Walk] at h
      obtain ⟨c, hc, hct⟩ := h
      exact (ih hc).tail hct

end Walk

/-- Directed reachability can be witnessed by a walk of some natural length. -/
theorem reach_walk {n : ℕ} {G : Digraph n} {s t : Vertex n} (h : G.Reach s t) :
    ∃ m : ℕ, Walk G m s t := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hbc ih =>
      obtain ⟨m, hm⟩ := ih
      exact ⟨m + 1, _, hm, hbc⟩

namespace DFSTree

variable {n : ℕ} {G : UndirectedMatrix n}

/-- A walk from `s` to a distinct `t` implies that `t` is a descendant of `s` if every other
vertex reachable from `s` and able to reach `t` has later discovery time than `s`
[DurrMhallaLei2003]. -/
theorem descendant_of_walk_disc_gt (T : DFSTree n G) {s : Vertex n} :
    ∀ (m : ℕ) {t : Vertex n}, Walk G.toDigraph m s t → s ≠ t →
      (∀ z : Vertex n, G.toDigraph.Reach s z → G.toDigraph.Reach z t → s ≠ z →
        T.disc s < T.disc z) →
      Descendant T.parent s t := by
  intro m
  induction m with
  | zero =>
      intro t hwalk hne _
      simp only [Walk] at hwalk
      subst hwalk
      exact absurd rfl hne
  | succ m ih =>
      intro t hwalk hne hwhite
      simp only [Walk] at hwalk
      obtain ⟨c, hc, hct⟩ := hwalk
      by_cases hsc : s = c
      · subst hsc
        have hst : G.toDigraph.Reach s t :=
          Walk.reach (G := G.toDigraph) (m := m + 1) ⟨s, hc, hct⟩
        exact T.no_cross s t hct (hwhite t hst Relation.ReflTransGen.refl hne)
      · have hdesc : Descendant T.parent s c :=
          ih hc hsc (fun z hsz hzc hz => hwhite z hsz (hzc.tail hct) hz)
        have hct_ne : c ≠ t := by
          intro hct_eq
          subst hct_eq
          simp [UndirectedMatrix.toDigraph, G.loopless] at hct
        have hst : G.toDigraph.Reach s t :=
          Walk.reach (G := G.toDigraph) (m := m + 1) ⟨c, hc, hct⟩
        rcases lt_trichotomy (T.disc c) (T.disc t) with hlt | heq | hgt
        · exact hdesc.trans (T.no_cross c t hct hlt)
        · exact absurd (T.disc_injective heq) hct_ne
        · have hadj : G.toDigraph.adj t c = true := by
            simp only [UndirectedMatrix.toDigraph] at hct ⊢
            exact (G.symm t c).trans hct
          have hback : Descendant T.parent t c := T.no_cross t c hadj hgt
          exact T.descendant_of_descendant_of_disc_lt hdesc hback
            (hwhite t hst Relation.ReflTransGen.refl hne)

/-- If `t` is reachable from a distinct `s` and every other vertex lying on a walk from `s` to
`t` has later discovery time, then `t` is a descendant of `s` [DurrMhallaLei2003]. -/
theorem descendant_of_path_disc_gt (T : DFSTree n G) {s t : Vertex n}
    (hpath : G.toDigraph.Reach s t) (hne : s ≠ t)
    (hwhite : ∀ z : Vertex n, G.toDigraph.Reach s z → G.toDigraph.Reach z t → s ≠ z →
      T.disc s < T.disc z) :
    Descendant T.parent s t := by
  obtain ⟨m, hm⟩ := reach_walk hpath
  exact T.descendant_of_walk_disc_gt m hm hne hwhite

/-- A descendant chain in a DFS tree gives reachability in the underlying graph. -/
theorem reach_of_descendant (T : DFSTree n G) {u v : Vertex n}
    (h : Descendant T.parent u v) : G.toDigraph.Reach u v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (T.parent_edge _ _ hbc)

/-- An undirected graph possessing a spanning `DFSTree` is connected [DurrMhallaLei2003]. -/
theorem connected (T : DFSTree n G) : G.Connected := by
  intro s t
  have hroot_s : G.toDigraph.Reach T.root s := T.reach_of_descendant (T.spanning s)
  have hroot_t : G.toDigraph.Reach T.root t := T.reach_of_descendant (T.spanning t)
  exact (G.reach_symm hroot_s).trans hroot_t

/-- Under the stated discovery-order condition on every vertex other than `u` reachable from `u`
and able to reach a distinct `w`, reachability from `u` to `w` implies that `w` is a
descendant of `u` [DurrMhallaLei2003]. -/
theorem lemma1_corrected (T : DFSTree n G) {u w : Vertex n}
    (hpath : G.toDigraph.Reach u w) (hne : u ≠ w)
    (hwhite : ∀ z : Vertex n, G.toDigraph.Reach u z → G.toDigraph.Reach z w →
      u ≠ z → T.disc u < T.disc z) :
    Descendant T.parent u w :=
  T.descendant_of_path_disc_gt hpath hne hwhite

end DFSTree

/-- The DFS search count for any visited subset is at most twice the total number of vertices
[DurrMhallaLei2003]. -/
theorem dfsSearchCount_le {n : ℕ} (visited : Finset (Vertex n)) :
    dfsSearchCount visited ≤ 2 * n := by
  unfold dfsSearchCount
  have hcard : visited.card ≤ n := by
    have := Finset.card_le_univ visited
    simpa [Vertex, Fintype.card_fin] using this
  omega

end Qatlib.Papers.GraphConnect03.MainResults.UpperBounds
