/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Combinatorics.SimpleGraph.Clique
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Foundations.GraphMoves.IndepInsert

universe u
variable {V : Type u}

def NoSelectedNeighbor (G : SimpleGraph V) (w : V) (S : Set V) : Prop :=
  ∀ v ∈ S, ¬ G.Adj w v

theorem independent_empty (G : SimpleGraph V) : G.IsIndepSet (∅ : Set V) := by
  intro v hv
  exact False.elim hv

theorem independent_remove (G : SimpleGraph V) (S : Set V) (w : V)
    (hS : G.IsIndepSet S) : G.IsIndepSet (S \ {w}) := by
  intro v hv z hz hne
  exact hS hv.1 hz.1 hne

theorem independent_insert_iff (G : SimpleGraph V) (S : Set V) (w : V) :
    G.IsIndepSet (insert w S) ↔ G.IsIndepSet S ∧ NoSelectedNeighbor G w S := by
  constructor
  · intro h
    constructor
    · intro v hv z hz hne
      exact h (Or.inr hv) (Or.inr hz) hne
    · intro v hv edge
      have hne : w ≠ v := by
        intro heq
        subst v
        exact G.irrefl edge
      exact h (Or.inl rfl) (Or.inr hv) hne edge
  · intro h v hv z hz hne
    change v = w ∨ v ∈ S at hv
    change z = w ∨ z ∈ S at hz
    rcases hv with hv | hv
    · subst v
      rcases hz with hz | hz
      · subst z
        exact G.irrefl
      · exact h.2 z hz
    · rcases hz with hz | hz
      · subst z
        exact fun edge => h.2 v hv (G.adj_symm edge)
      · exact h.1 hv hz hne

theorem independent_insert_of_no_neighbors (G : SimpleGraph V) (S : Set V) (w : V)
    (hS : G.IsIndepSet S) (hN : NoSelectedNeighbor G w S) :
    G.IsIndepSet (insert w S) :=
  (independent_insert_iff G S w).2 ⟨hS, hN⟩

end Qatlib.Foundations.GraphMoves.IndepInsert
