/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.UnitaryDigraph.MainResults.Defs
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace Qatlib.Papers.UnitaryDigraph.MainResults.LineDigraph

open Qatlib.Papers.UnitaryDigraph.MainResults.Defs
open Qatlib.Papers.UnitaryDigraph.MainResults.Defs.Digraph

theorem theorem2_i_out {V : Type} (D : Digraph V) (a : Arc D) :
    (lineDigraph D).outNbrs a = {b : Arc D | b.1.1 = a.1.2} := by
  ext b
  rw [mem_outNbrs]
  exact eq_comm

theorem theorem2_i_in {V : Type} (D : Digraph V) (a : Arc D) :
    (lineDigraph D).inNbrs a = {b : Arc D | b.1.2 = a.1.1} := by
  ext b
  rw [mem_inNbrs]
  exact Iff.rfl

theorem lineDigraph_specular {V : Type} (D : Digraph V) : Specular (lineDigraph D) := by
  constructor
  · intro a b _ hint
    have h : a.1.2 = b.1.2 := by
      obtain ⟨c, hc⟩ := hint
      simp only [Set.mem_inter_iff, theorem2_i_out D a, theorem2_i_out D b,
        Set.mem_setOf_eq] at hc
      exact hc.1.symm.trans hc.2
    ext d
    simp [theorem2_i_out D a, theorem2_i_out D b, h]
  · intro a b _ hint
    have h : a.1.1 = b.1.1 := by
      obtain ⟨c, hc⟩ := hint
      simp only [Set.mem_inter_iff, theorem2_i_in D a, theorem2_i_in D b,
        Set.mem_setOf_eq] at hc
      exact hc.1.symm.trans hc.2
    ext d
    simp [theorem2_i_in D a, theorem2_i_in D b, h]

theorem specular_of_isomorphic {V W : Type} {D : Digraph V} {D' : Digraph W}
    (h : Isomorphic D D') (hs : Specular D') : Specular D := by
  obtain ⟨e, he⟩ := h
  have hout : ∀ i : V, D.outNbrs i = e ⁻¹' (D'.outNbrs (e i)) := by
    intro i; ext j
    simp only [mem_outNbrs, Set.mem_preimage]
    exact he i j
  have hin : ∀ i : V, D.inNbrs i = e ⁻¹' (D'.inNbrs (e i)) := by
    intro i; ext j
    simp only [mem_inNbrs, Set.mem_preimage]
    exact he j i
  constructor
  · intro i j hij hint
    have hne : e i ≠ e j := fun hh => hij (e.injective hh)
    have h' : (D'.outNbrs (e i) ∩ D'.outNbrs (e j)).Nonempty := by
      obtain ⟨c, hc⟩ := hint
      exact ⟨e c, (hout i).le hc.1, (hout j).le hc.2⟩
    ext x
    have hE := hs.1 (e i) (e j) hne h'
    rw [hout i, hout j, hE]
  · intro i j hij hint
    have hne : e i ≠ e j := fun hh => hij (e.injective hh)
    have h' : (D'.inNbrs (e i) ∩ D'.inNbrs (e j)).Nonempty := by
      obtain ⟨c, hc⟩ := hint
      exact ⟨e c, (hin i).le hc.1, (hin j).le hc.2⟩
    ext x
    have hE := hs.2 (e i) (e j) hne h'
    rw [hin i, hin j, hE]

theorem specular_of_isLineDigraph {V : Type} (D : Digraph V) (h : IsLineDigraph D) :
    Specular D := by
  obtain ⟨W, D₀, hiso⟩ := h
  exact specular_of_isomorphic hiso (lineDigraph_specular D₀)

end Qatlib.Papers.UnitaryDigraph.MainResults.LineDigraph
