/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.UnitaryDigraph.MainResults.Defs
import Qatlib.Papers.UnitaryDigraph.MainResults.Complete

/-!
# Unitary realizations of specular digraphs

This module constructs unitary realizations for finite specular digraphs with incoming and
outgoing strong quadrangularity and nonempty neighborhoods. The theorem `theorem1` gives this
formulation of Theorem 1 of [Severini2003]; auxiliary results express distinct neighborhood
blocks as disjoint sets.

## Main statements

* `theorem1`: Realize a specular digraph under the stated quadrangularity and nonemptiness
  hypotheses.
* `specular_outNbrs_disjoint`: Unequal outgoing neighborhoods at distinct vertices are disjoint.

## References

* [Severini, 2003][Severini2003]
-/

set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace Qatlib.Papers.UnitaryDigraph.MainResults.Specular

open Qatlib.Papers.UnitaryDigraph.MainResults.Defs

/-- In a specular digraph, unequal outgoing neighborhoods of distinct vertices are disjoint
[Severini2003]. -/
theorem specular_outNbrs_disjoint {V : Type} {D : Defs.Digraph V} (hs : Specular D)
    {i j : V} (hij : i ≠ j) (hne : D.outNbrs i ≠ D.outNbrs j) :
    Disjoint (D.outNbrs i) (D.outNbrs j) := by
  rw [Set.disjoint_left]
  intro x hi hj
  exact hne (hs.1 i j hij ⟨x, hi, hj⟩)

/-- In a specular digraph, unequal incoming neighborhoods of distinct vertices are disjoint
[Severini2003]. -/
theorem specular_inNbrs_disjoint {V : Type} {D : Defs.Digraph V} (hs : Specular D)
    {i j : V} (hij : i ≠ j) (hne : D.inNbrs i ≠ D.inNbrs j) :
    Disjoint (D.inNbrs i) (D.inNbrs j) := by
  rw [Set.disjoint_left]
  intro x hi hj
  exact hne (hs.2 i j hij ⟨x, hi, hj⟩)

end Qatlib.Papers.UnitaryDigraph.MainResults.Specular

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace Qatlib.Papers.UnitaryDigraph.MainResults.Specular

open Qatlib.Papers.UnitaryDigraph.MainResults.Defs
open Qatlib.Papers.UnitaryDigraph.MainResults.Defs.Digraph
open Qatlib.Papers.UnitaryDigraph.MainResults.Complete
open Matrix

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A set with at least two elements contains a member distinct from any specified member. -/
theorem exists_mem_ne_of_two_le_ncard {W : Type*} {S : Set W} (h2 : 2 ≤ S.ncard) {i : W}
    (_hi : i ∈ S) : ∃ j ∈ S, j ≠ i := by
  by_contra h
  push Not at h
  have hsub : S ⊆ ({i} : Set W) := fun j hj => by
    rw [Set.mem_singleton_iff]
    exact h j hj
  have hle : S.ncard ≤ ({i} : Set W).ncard := Set.ncard_le_ncard hsub
  rw [Set.ncard_singleton] at hle
  omega

/-- A finite specular digraph is unitary if it is both incoming and outgoing strongly
quadrangular and every incoming and outgoing neighborhood is nonempty [Severini2003]. -/
theorem theorem1 (D : Defs.Digraph V) (hspec : Specular D)
    (houtSQ : OutStronglyQuadrangular D) (hinSQ : InStronglyQuadrangular D)
    (hout : ∀ v, (D.outNbrs v).Nonempty) (hin : ∀ v, (D.inNbrs v).Nonempty) :
    IsUnitaryDigraph D := by
  classical
  let N : V → Finset V := fun i => Finset.univ.filter (fun j => D.Adj i j)
  have N_coe : ∀ i, (N i : Set V) = D.outNbrs i := by
    intro i; ext j; simp [N, mem_outNbrs]
  let c : V → Finset V := fun j => N (Classical.choose (hin j))
  have c_def : ∀ j, c j = N (Classical.choose (hin j)) := fun _ => rfl
  have c_self : ∀ j, j ∈ (c j : Set V) := by
    intro j
    rw [c_def j, N_coe]
    exact mem_outNbrs.mpr (mem_inNbrs.mp (Classical.choose_spec (hin j)))
  have c_eq_of_mem : ∀ i j, j ∈ (N i : Set V) → c j = N i := by
    intro i j hj
    set k := Classical.choose (hin j) with hk
    have hjOut : j ∈ D.outNbrs i := by rwa [N_coe] at hj
    have hk_mem : j ∈ D.outNbrs k := by
      rw [hk]
      exact mem_outNbrs.mpr (mem_inNbrs.mp (Classical.choose_spec (hin j)))
    have hinter : (D.outNbrs i ∩ D.outNbrs k).Nonempty := ⟨j, hjOut, hk_mem⟩
    have hEq : D.outNbrs i = D.outNbrs k := by
      by_cases hik : i = k
      · rw [hik]
      · exact hspec.1 i k hik hinter
    show c j = N i
    rw [c_def j]
    exact Finset.coe_inj.mp (by rw [N_coe, N_coe, hEq])
  have hAdj : ∀ i j, D.Adj i j ↔ N i = c j := by
    intro i j
    constructor
    · intro h
      have hj : j ∈ (N i : Set V) := by rw [N_coe]; exact mem_outNbrs.mpr h
      exact (c_eq_of_mem i j hj).symm
    · intro h
      have hj : j ∈ (N i : Set V) := by rw [h]; exact c_self j
      rw [N_coe] at hj
      exact mem_outNbrs.mp hj

  have c_iff : ∀ (α : Finset V), (∃ k, N k = α) → ∀ j, c j = α ↔ j ∈ (α : Set V) := by
    intro α hα j
    constructor
    · intro h
      have := c_self j
      rwa [h] at this
    · intro hj
      obtain ⟨k, hk⟩ := hα
      have hjN : j ∈ (N k : Set V) := by rw [hk]; exact hj
      rw [c_eq_of_mem k j hjN, hk]
  have hcard_realized : ∀ α : Finset V, (∃ k, N k = α) →
      Nat.card {i : V // N i = α} = Nat.card {j : V // c j = α} := by
    intro α hα
    obtain ⟨k0, hk0⟩ := hα

    have hApos : 0 < ((α : Set V)).ncard := by
      rw [← hk0, N_coe]
      exact (Set.ncard_pos (s := D.outNbrs k0)).mpr (hout k0)

    have hRpos : 0 < ({i : V | N i = α} : Set V).ncard := by
      exact (Set.ncard_pos (s := {i : V | N i = α})).mpr ⟨k0, hk0⟩

    have hRA : ({i : V | N i = α} : Set V).ncard ≤ ((α : Set V)).ncard := by
      by_contra hle
      rw [not_le] at hle
      refine houtSQ ⟨{i : V | N i = α}, (α : Set V), hle, ?_, ?_⟩
      · intro i hi
        have hOi : D.outNbrs i = (α : Set V) := by
          rw [← N_coe, show N i = α from hi]
        have hS2 : 2 ≤ ({i : V | N i = α} : Set V).ncard := by omega
        obtain ⟨j, hjR, hjne⟩ :=
          exists_mem_ne_of_two_le_ncard hS2 (i := i) (by exact hi)
        have hOj : D.outNbrs j = (α : Set V) := by
          rw [← N_coe, show N j = α from hjR]
        have hOthers : D.outNbrsOthers {i : V | N i = α} i = (α : Set V) := by
          apply Set.Subset.antisymm
          · intro x hx
            simp only [outNbrsOthers, Set.mem_iUnion, exists_prop] at hx
            obtain ⟨j', hj'R, -, hxj'⟩ := hx
            have hOj' : D.outNbrs j' = (α : Set V) := by
              rw [← N_coe, show N j' = α from hj'R]
            rwa [hOj'] at hxj'
          · intro x hx
            exact mem_outNbrsOthers (S := {i : V | N i = α}) (i := i) (j := j) hjR hjne
              (by rw [hOj]; exact hx)
        obtain ⟨x, hx⟩ := (Set.ncard_pos (s := (α : Set V))).mp hApos
        refine ⟨x, ?_, ?_⟩
        · rw [hOi]; exact hx
        · rw [hOthers]; exact hx
      · intro a ha b hb _
        have hOa : D.outNbrs a = (α : Set V) := by
          rw [← N_coe, show N a = α from ha]
        have hOb : D.outNbrs b = (α : Set V) := by
          rw [← N_coe, show N b = α from hb]
        intro x hx
        rw [hOa, hOb] at hx
        exact hx.1

    have inNbrs_eq : ∀ j, j ∈ (α : Set V) → D.inNbrs j = {i : V | N i = α} := by
      intro j hj
      have hjN : j ∈ (N k0 : Set V) := by rw [hk0]; exact hj
      have hjOutk : j ∈ D.outNbrs k0 := by rwa [N_coe] at hjN
      ext i
      constructor
      · intro hij
        have hij' : D.Adj i j := mem_inNbrs.mp hij
        have hjOuti : j ∈ D.outNbrs i := mem_outNbrs.mpr hij'
        have hEq : D.outNbrs i = D.outNbrs k0 := by
          by_cases hik : i = k0
          · rw [hik]
          · exact hspec.1 i k0 hik ⟨j, hjOuti, hjOutk⟩
        show N i = α
        rw [← hk0]
        exact Finset.coe_inj.mp (by rw [N_coe, N_coe, hEq])
      · intro hiR
        have hNi : N i = α := hiR
        have hjNi : j ∈ (N i : Set V) := by rw [hNi]; exact hj
        rw [N_coe] at hjNi
        exact mem_inNbrs.mpr (mem_outNbrs.mp hjNi)

    have hAR : ((α : Set V)).ncard ≤ ({i : V | N i = α} : Set V).ncard := by
      by_contra hle
      rw [not_le] at hle
      refine hinSQ ⟨(α : Set V), {i : V | N i = α}, hle, ?_, ?_⟩
      · intro j hj
        have hInj : D.inNbrs j = {i : V | N i = α} := inNbrs_eq j hj
        have hS2 : 2 ≤ ((α : Set V)).ncard := by omega
        obtain ⟨j', hj'A, hj'ne⟩ :=
          exists_mem_ne_of_two_le_ncard hS2 (i := j) (by exact hj)
        have hInj' : D.inNbrs j' = {i : V | N i = α} := inNbrs_eq j' hj'A
        have hOthers : D.inNbrsOthers (α : Set V) j = {i : V | N i = α} := by
          apply Set.Subset.antisymm
          · intro x hx
            simp only [inNbrsOthers, Set.mem_iUnion, exists_prop] at hx
            obtain ⟨y, hyA, -, hxy⟩ := hx
            have hIny : D.inNbrs y = {i : V | N i = α} := inNbrs_eq y hyA
            rwa [hIny] at hxy
          · intro x hx
            exact mem_inNbrsOthers (S := (α : Set V)) (i := j) (j := j') hj'A hj'ne
              (by rw [hInj']; exact hx)
        obtain ⟨x, hx⟩ := (Set.ncard_pos (s := {i : V | N i = α})).mp hRpos
        refine ⟨x, ?_, ?_⟩
        · rw [hInj]; exact hx
        · rw [hOthers]; exact hx
      · intro a ha b hb _
        have hIna : D.inNbrs a = {i : V | N i = α} := inNbrs_eq a ha
        have hInb : D.inNbrs b = {i : V | N i = α} := inNbrs_eq b hb
        intro x hx
        rw [hIna, hInb] at hx
        exact hx.1
    have hRnat : Nat.card {i : V // N i = α} = ({i : V | N i = α} : Set V).ncard :=
      Nat.card_coe_set_eq _
    have hCnat : Nat.card {j : V // c j = α} = ((α : Set V)).ncard := by
      have hset : ({j : V | c j = α} : Set V) = (α : Set V) := by
        ext j; exact c_iff α ⟨k0, hk0⟩ j
      calc Nat.card {j : V // c j = α} = Nat.card ↥({j : V | c j = α} : Set V) := rfl
        _ = ({j : V | c j = α} : Set V).ncard := Nat.card_coe_set_eq _
        _ = ((α : Set V)).ncard := by rw [hset]
    rw [hRnat, hCnat, le_antisymm hRA hAR]
  have hcard_empty : ∀ α : Finset V, (¬ ∃ k, N k = α) →
      Nat.card {i : V // N i = α} = Nat.card {j : V // c j = α} := by
    intro α hα
    have hR0 : Nat.card {i : V // N i = α} = 0 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff]
      exact ⟨fun x => hα ⟨x.1, x.2⟩⟩
    have hC0 : Nat.card {j : V // c j = α} = 0 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff]
      exact ⟨fun x => hα ⟨Classical.choose (hin x.1), x.2⟩⟩
    rw [hR0, hC0]
  have hcard : ∀ α : Finset V,
      Nat.card {i : V // N i = α} = Nat.card {j : V // c j = α} := by
    intro α
    by_cases hα : ∃ k, N k = α
    · exact hcard_realized α hα
    · exact hcard_empty α hα
  exact isUnitaryDigraph_of_fiber_complete D N c hAdj hcard

end Qatlib.Papers.UnitaryDigraph.MainResults.Specular
