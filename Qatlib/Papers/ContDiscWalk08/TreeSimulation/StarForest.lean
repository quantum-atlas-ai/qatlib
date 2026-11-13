/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ContDiscWalk08.TreeSimulation.StarSpectrum

/-!
# Depth parity and star decomposition

The structure `RootedTree` records a parent map, a depth function increasing along child edges,
and a distinguished depth-zero vertex. The module defines the parent adjacency and its
depth-selected star matrices, then splits adjacency into the even-center and odd-center parts
used in the tree simulation discussion of [Childs2010].

## Main statements

* `edge_parity`: parent edges join opposite depth parities.
* `starEdge_iff_of_parent`: the parent determines the star center.
* `treeAdjacency_eq_forests`: even-center and odd-center matrices sum to the adjacency.

## References

* [Childs, 2010][Childs2010]
-/

set_option autoImplicit false

noncomputable section

open Matrix

namespace Qatlib.Papers.ContDiscWalk08.TreeSimulation

/-- Records a parent map, a natural-valued depth function, and a distinguished vertex of depth
zero, with every child one level deeper than its parent. -/
structure RootedTree (N : ℕ) where

  parent : Fin N → Option (Fin N)

  depth : Fin N → ℕ

  root : Fin N

  depth_root : depth root = 0

  parent_depth : ∀ v q, parent v = some q → depth v = depth q + 1

variable {N : ℕ} (T : RootedTree N)

/-- Defines adjacency by the condition that either endpoint is the parent of the other. -/
abbrev IsTreeEdge (T : RootedTree N) (u v : Fin N) : Prop :=
  T.parent u = some v ∨ T.parent v = some u

/-- A vertex cannot be its own parent when depth increases by one along child edges. -/
theorem parent_ne_self (T : RootedTree N) (v : Fin N) (q : Fin N)
    (h : T.parent v = some q) : q ≠ v := by
  intro hqv
  have hd := T.parent_depth v q h
  rw [hqv] at hd
  omega

/-- If `v` is the parent of `u`, then `u` is not the parent of `v`. -/
theorem parent_not_symm (T : RootedTree N) {u v : Fin N}
    (h : T.parent u = some v) : T.parent v ≠ some u := by
  intro h2
  have h1 := T.parent_depth u v h
  have h2' := T.parent_depth v u h2
  omega

/-- Natural numbers differing by one have opposite parity. -/
theorem parity_step {a b : ℕ} (h : a = b + 1) :
    (Even a ∧ Odd b) ∨ (Odd a ∧ Even b) := by
  rcases Nat.even_or_odd b with hb | hb
  · right
    refine ⟨Nat.odd_iff.mpr ?_, hb⟩
    have hb' : b % 2 = 0 := Nat.even_iff.mp hb
    rw [h]
    omega
  · left
    refine ⟨Nat.even_iff.mpr ?_, hb⟩
    have hb' : b % 2 = 1 := Nat.odd_iff.mp hb
    rw [h]
    omega

/-- Every parent edge joins vertices of opposite depth parity. This gives the parity separation
used for tree simulation in [Childs2010]. -/
theorem edge_parity {u v : Fin N} (h : IsTreeEdge T u v) :
    (Even (T.depth u) ∧ Odd (T.depth v)) ∨
      (Odd (T.depth u) ∧ Even (T.depth v)) := by
  unfold IsTreeEdge at h
  rcases h with h | h
  · exact parity_step (T.parent_depth u v h)
  · rcases parity_step (T.parent_depth v u h) with h' | h'
    · right; exact ⟨h'.2, h'.1⟩
    · left; exact ⟨h'.2, h'.1⟩

/-- Defines an edge joining the center `c` to one of its children, in either orientation. -/
abbrev starEdge (T : RootedTree N) (c u v : Fin N) : Prop :=
  (T.parent u = some c ∧ v = c) ∨ (T.parent v = some c ∧ u = c)

/-- Every edge of a parent-centered star is a parent adjacency edge. -/
theorem starEdge_isTreeEdge {c u v : Fin N} (h : starEdge T c u v) :
    IsTreeEdge T u v := by
  unfold starEdge at h
  unfold IsTreeEdge
  rcases h with ⟨hp, hvc⟩ | ⟨hp, huc⟩
  · left; rw [hvc]; exact hp
  · right; rw [huc]; exact hp

/-- If `v` is the parent of `u`, their edge belongs to the star centered at `c` exactly when `c
= v`. This identifies the star center in the decomposition of [Childs2010]. -/
theorem starEdge_iff_of_parent {u v : Fin N} (h : T.parent u = some v) :
    ∀ c : Fin N, starEdge T c u v ↔ c = v := by
  intro c
  constructor
  · intro hs
    unfold starEdge at hs
    rcases hs with ⟨hp, hvc⟩ | ⟨hp, huc⟩
    · exact hvc.symm
    · subst huc
      exact absurd hp (parent_not_symm T h)
  · intro hc
    subst hc
    exact Or.inl ⟨h, rfl⟩

/-- If `u` is the parent of `v`, their edge belongs to the star centered at `c` exactly when `c
= u`. -/
theorem starEdge_iff_of_parent' {u v : Fin N} (h : T.parent v = some u) :
    ∀ c : Fin N, starEdge T c u v ↔ c = u := by
  intro c
  constructor
  · intro hs
    unfold starEdge at hs
    rcases hs with ⟨hp, hvc⟩ | ⟨hp, huc⟩
    · subst hvc
      exact absurd hp (parent_not_symm T h)
    · exact huc.symm
  · intro hc
    subst hc
    exact Or.inr ⟨h, rfl⟩

/-- Defines the zero-one adjacency matrix of the parent-edge relation. -/
def treeAdjacency (T : RootedTree N) : Matrix (Fin N) (Fin N) ℂ :=
  fun u v => if IsTreeEdge T u v then 1 else 0

/-- Defines the zero-one matrix selecting star edges whose center depth satisfies `S`, as used
in the parity decomposition of [Childs2010]. -/
def forestMatrix (T : RootedTree N) (S : ℕ → Prop) [DecidablePred S] :
    Matrix (Fin N) (Fin N) ℂ :=
  fun u v => if ∃ c, S (T.depth c) ∧ starEdge T c u v then 1 else 0

/-- Each adjacency entry is the sum of its even-center and odd-center star-matrix entries. This
is the parity decomposition used in [Childs2010]. -/
theorem treeAdjacency_eq_forests (u v : Fin N) :
    treeAdjacency T u v =
      forestMatrix T Even u v + forestMatrix T Odd u v := by
  unfold treeAdjacency forestMatrix
  by_cases h : IsTreeEdge T u v
  · rw [ite_eq_left h]

    have hmain : ∀ (w : Fin N), (∀ c, starEdge T c u v ↔ c = w) →
        (if ∃ c, Even (T.depth c) ∧ starEdge T c u v then (1 : ℂ) else 0) +
          (if ∃ c, Odd (T.depth c) ∧ starEdge T c u v then (1 : ℂ) else 0) = 1 := by
      intro w hstar
      have hE : (∃ c, Even (T.depth c) ∧ starEdge T c u v) ↔ Even (T.depth w) := by
        constructor
        · rintro ⟨c, hc, hs⟩
          rwa [(hstar c).mp hs] at hc
        · intro hc
          exact ⟨w, hc, (hstar w).mpr rfl⟩
      have hO : (∃ c, Odd (T.depth c) ∧ starEdge T c u v) ↔ Odd (T.depth w) := by
        constructor
        · rintro ⟨c, hc, hs⟩
          rwa [(hstar c).mp hs] at hc
        · intro hc
          exact ⟨w, hc, (hstar w).mpr rfl⟩
      by_cases hb : Even (T.depth w)
      · rw [ite_eq_left (hE.mpr hb),
          ite_eq_right (fun ho => (Nat.not_even_iff_odd.mpr (hO.mp ho)) hb)]
        norm_num
      · have hb' : Odd (T.depth w) := by
          rcases Nat.even_or_odd (T.depth w) with h' | h'
          · exact absurd h' hb
          · exact h'
        rw [ite_eq_right (fun he => hb (hE.mp he)), ite_eq_left (hO.mpr hb')]
        norm_num
    rcases h with h1 | h1
    · exact (hmain v (starEdge_iff_of_parent T h1)).symm
    · exact (hmain u (starEdge_iff_of_parent' T h1)).symm
  · rw [ite_eq_right h]
    have hE : ¬ ∃ c, Even (T.depth c) ∧ starEdge T c u v :=
      fun ⟨c, _, hsc⟩ => h (starEdge_isTreeEdge T hsc)
    have hO : ¬ ∃ c, Odd (T.depth c) ∧ starEdge T c u v :=
      fun ⟨c, _, hsc⟩ => h (starEdge_isTreeEdge T hsc)
    rw [ite_eq_right hE, ite_eq_right hO]
    norm_num

end Qatlib.Papers.ContDiscWalk08.TreeSimulation
