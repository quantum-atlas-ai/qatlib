/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.UnitaryDigraph.MainResults.Complete
import Qatlib.Papers.UnitaryDigraph.MainResults.LineDigraph.Theorem2
import Qatlib.Papers.UnitaryDigraph.MainResults.Defs
import Qatlib.Papers.UnitaryDigraph.MainResults.Quadrangular
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace Qatlib.Papers.UnitaryDigraph.MainResults.Eulerian

open Qatlib.Papers.UnitaryDigraph.MainResults.Defs

theorem lineDigraph_adj_iff {V : Type} (D : Defs.Digraph V) (a b : Arc D) :
    (lineDigraph D).Adj a b ↔ a.1.2 = b.1.1 :=
  Iff.rfl

theorem lineDigraph_adj_decomp {V : Type} (D : Defs.Digraph V) (a b : Arc D) :
    (lineDigraph D).Adj a b ↔ ∃ v : V, a.1.2 = v ∧ b.1.1 = v := by
  rw [lineDigraph_adj_iff]
  constructor
  · intro h; exact ⟨b.1.1, h, rfl⟩
  · rintro ⟨v, h1, h2⟩; exact h1.trans h2.symm

theorem lineDigraph_adj_blocks {V : Type} (D : Defs.Digraph V) (a b : Arc D) :
    (lineDigraph D).Adj a b ↔
      ∃ v : V, a ∈ {x : Arc D | x.1.2 = v} ∧ b ∈ {x : Arc D | x.1.1 = v} := by
  rw [lineDigraph_adj_decomp]
  simp

open Qatlib.Papers.UnitaryDigraph.MainResults.Quadrangular
open Qatlib.Papers.UnitaryDigraph.MainResults.LineDigraph
open Qatlib.Papers.UnitaryDigraph.MainResults.Complete

open Qatlib.Papers.UnitaryDigraph.MainResults.Defs
open Qatlib.Papers.UnitaryDigraph.MainResults.Defs.Digraph

def outArcs {V : Type} (D : Defs.Digraph V) (v : V) : Set (Arc D) := {b | b.1.1 = v}

def inArcs {V : Type} (D : Defs.Digraph V) (v : V) : Set (Arc D) := {a | a.1.2 = v}

theorem ncard_inArcs {V : Type} [Fintype V] {D : Defs.Digraph V} [Fintype (Arc D)] (v : V) :
    (inArcs D v).ncard = (D.inNbrs v).ncard := by
  classical
  refine Set.ncard_congr' (Equiv.ofBijective
    (fun a : {a : Arc D // a ∈ inArcs D v} =>
      (⟨a.1.1.1, ?_⟩ : {u : V // u ∈ D.inNbrs v})) ?_)
  · have ha : a.1.1.2 = v := a.2
    simpa [← ha] using a.1.2
  · constructor
    · rintro ⟨a, ha⟩ ⟨b, hb⟩ heq
      simp only [Subtype.mk.injEq] at heq
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · exact heq
      · exact ha.trans hb.symm
    · rintro ⟨u, hu⟩
      refine ⟨⟨⟨(u, v), mem_inNbrs.mp hu⟩, rfl⟩, ?_⟩
      rfl

theorem ncard_outArcs {V : Type} [Fintype V] {D : Defs.Digraph V} [Fintype (Arc D)] (v : V) :
    (outArcs D v).ncard = (D.outNbrs v).ncard := by
  classical
  refine Set.ncard_congr' (Equiv.ofBijective
    (fun b : {b : Arc D // b ∈ outArcs D v} =>
      (⟨b.1.1.2, ?_⟩ : {u : V // u ∈ D.outNbrs v})) ?_)
  · have hb : b.1.1.1 = v := b.2
    simpa [← hb] using b.1.2
  · constructor
    · rintro ⟨b, hb⟩ ⟨c, hc⟩ heq
      simp only [Subtype.mk.injEq] at heq
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · exact hb.trans hc.symm
      · exact heq
    · rintro ⟨u, hu⟩
      refine ⟨⟨⟨(v, u), mem_outNbrs.mp hu⟩, rfl⟩, ?_⟩
      rfl

theorem card_inArcs {V : Type} [Fintype V] {D : Defs.Digraph V} [Fintype (Arc D)] (v : V) :
    Nat.card {a : Arc D // a.1.2 = v} = (D.inNbrs v).ncard := by
  classical
  exact (Nat.card_coe_set_eq (inArcs D v)).trans (ncard_inArcs (D := D) v)

theorem card_outArcs {V : Type} [Fintype V] {D : Defs.Digraph V} [Fintype (Arc D)] (v : V) :
    Nat.card {b : Arc D // b.1.1 = v} = (D.outNbrs v).ncard := by
  classical
  exact (Nat.card_coe_set_eq (outArcs D v)).trans (ncard_outArcs (D := D) v)

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

theorem eulerian_of_unitary_lineDigraph {V : Type} [Fintype V] [DecidableEq V]
    (D : Defs.Digraph V) [Fintype (Arc D)] [DecidableEq (Arc D)]
    (hU : IsUnitaryDigraph (lineDigraph D)) : Eulerian D := by
  classical
  have houtSQ : OutStronglyQuadrangular (lineDigraph D) :=
    outStronglyQuadrangular_of_isUnitaryDigraph _ hU
  have hinSQ : InStronglyQuadrangular (lineDigraph D) :=
    inStronglyQuadrangular_of_isUnitaryDigraph _ hU
  have hrow : ∀ a : Arc D, ((lineDigraph D).outNbrs a).Nonempty :=
    fun a => outNbrs_nonempty_of_isUnitaryDigraph _ hU a
  have hcol : ∀ a : Arc D, ((lineDigraph D).inNbrs a).Nonempty :=
    fun a => inNbrs_nonempty_of_isUnitaryDigraph _ hU a
  intro v
  apply le_antisymm
  · by_contra hcon
    rw [not_le] at hcon
    have hinpos : 0 < (D.inNbrs v).ncard := by omega
    have houtpos : 0 < (D.outNbrs v).ncard := by
      by_contra h0
      rw [not_lt, Nat.le_zero_eq] at h0
      obtain ⟨u, hu⟩ := (Set.ncard_pos (s := D.inNbrs v)).mp hinpos
      have hu' : D.Adj u v := mem_inNbrs.mp hu
      let a : Arc D := ⟨(u, v), hu'⟩
      have hane := hrow a
      have hae : a.1.2 = v := rfl
      rw [theorem2_i_out D a] at hane
      rw [show a.1.2 = v from hae] at hane
      have hpos' : 0 < (outArcs D v).ncard := (Set.ncard_pos (s := outArcs D v)).mpr hane
      rw [ncard_outArcs] at hpos'
      omega
    have hS2 : 2 ≤ (inArcs D v).ncard := by
      rw [ncard_inArcs]; omega
    have hTpos : 0 < (outArcs D v).ncard := by rw [ncard_outArcs]; exact houtpos
    refine houtSQ ⟨inArcs D v, outArcs D v, ?_, ?_, ?_⟩
    · rw [ncard_outArcs, ncard_inArcs]; exact hcon
    · intro i hi
      have hOi : (lineDigraph D).outNbrs i = outArcs D v := by
        rw [theorem2_i_out D i, show i.1.2 = v from hi]
        rfl
      have hUn : (lineDigraph D).outNbrsOthers (inArcs D v) i = outArcs D v := by
        obtain ⟨j, hjS, hjne⟩ := exists_mem_ne_of_two_le_ncard hS2 hi
        ext c
        simp only [outNbrsOthers, Set.mem_iUnion, exists_prop]
        constructor
        · rintro ⟨k, hkS, -, hc⟩
          rw [theorem2_i_out D k, show k.1.2 = v from hkS] at hc
          exact hc
        · intro hc
          exact ⟨j, hjS, hjne, by
            rw [theorem2_i_out D j, show j.1.2 = v from hjS]
            exact hc⟩
      rw [hOi, hUn, Set.inter_self]
      exact (Set.ncard_pos (s := outArcs D v)).mp hTpos
    · intro i hi j hj _
      have hOi : (lineDigraph D).outNbrs i = outArcs D v := by
        rw [theorem2_i_out D i, show i.1.2 = v from hi]
        rfl
      have hOj : (lineDigraph D).outNbrs j = outArcs D v := by
        rw [theorem2_i_out D j, show j.1.2 = v from hj]
        rfl
      rw [hOi, hOj, Set.inter_self]
  · by_contra hcon
    rw [not_le] at hcon
    have houtpos : 0 < (D.outNbrs v).ncard := by omega
    have hinpos : 0 < (D.inNbrs v).ncard := by
      by_contra h0
      rw [not_lt, Nat.le_zero_eq] at h0
      obtain ⟨u, hu⟩ := (Set.ncard_pos (s := D.outNbrs v)).mp houtpos
      have hu' : D.Adj v u := mem_outNbrs.mp hu
      let a : Arc D := ⟨(v, u), hu'⟩
      have hane := hcol a
      have hae : a.1.1 = v := rfl
      rw [theorem2_i_in D a] at hane
      rw [show a.1.1 = v from hae] at hane
      have hpos' : 0 < (inArcs D v).ncard := (Set.ncard_pos (s := inArcs D v)).mpr hane
      rw [ncard_inArcs] at hpos'
      omega
    have hS2 : 2 ≤ (outArcs D v).ncard := by rw [ncard_outArcs]; omega
    have hTpos : 0 < (inArcs D v).ncard := by rw [ncard_inArcs]; exact hinpos
    refine hinSQ ⟨outArcs D v, inArcs D v, ?_, ?_, ?_⟩
    · rw [ncard_inArcs, ncard_outArcs]; exact hcon
    · intro i hi
      have hIi : (lineDigraph D).inNbrs i = inArcs D v := by
        rw [theorem2_i_in D i, show i.1.1 = v from hi]
        rfl
      have hUn : (lineDigraph D).inNbrsOthers (outArcs D v) i = inArcs D v := by
        obtain ⟨j, hjS, hjne⟩ := exists_mem_ne_of_two_le_ncard hS2 hi
        ext c
        simp only [inNbrsOthers, Set.mem_iUnion, exists_prop]
        constructor
        · rintro ⟨k, hkS, -, hc⟩
          rw [theorem2_i_in D k, show k.1.1 = v from hkS] at hc
          exact hc
        · intro hc
          exact ⟨j, hjS, hjne, by
            rw [theorem2_i_in D j, show j.1.1 = v from hjS]
            exact hc⟩
      rw [hIi, hUn, Set.inter_self]
      exact (Set.ncard_pos (s := inArcs D v)).mp hTpos
    · intro i hi j hj _
      have hIi : (lineDigraph D).inNbrs i = inArcs D v := by
        rw [theorem2_i_in D i, show i.1.1 = v from hi]
        rfl
      have hIj : (lineDigraph D).inNbrs j = inArcs D v := by
        rw [theorem2_i_in D j, show j.1.1 = v from hj]
        rfl
      rw [hIi, hIj, Set.inter_self]

theorem isUnitaryDigraph_lineDigraph_of_eulerian {V : Type} [Fintype V] [DecidableEq V]
    (D : Defs.Digraph V) [Fintype (Arc D)] [DecidableEq (Arc D)] (hE : Eulerian D) :
    IsUnitaryDigraph (lineDigraph D) := by
  classical
  let r : Arc D → V := fun a => a.1.2
  let c : Arc D → V := fun b => b.1.1
  refine isUnitaryDigraph_of_fiber_complete (lineDigraph D) r c ?_ ?_
  · intro i j
    show (lineDigraph D).Adj i j ↔ r i = c j
    rfl
  · intro k
    have hfr : Nat.card {a : Arc D // r a = k} = (D.inNbrs k).ncard := by
      rw [Nat.card_congr (Equiv.subtypeEquivRight (fun a => by
        show r a = k ↔ a.1.2 = k
        rfl))]
      exact card_inArcs (D := D) k
    have hfc : Nat.card {b : Arc D // c b = k} = (D.outNbrs k).ncard := by
      rw [Nat.card_congr (Equiv.subtypeEquivRight (fun b => by
        show c b = k ↔ b.1.1 = k
        rfl))]
      exact card_outArcs (D := D) k
    rw [hfr, hfc, hE k]

theorem theorem3 {V : Type} [Fintype V] [DecidableEq V]
    (D : Defs.Digraph V) [Fintype (Arc D)] [DecidableEq (Arc D)] :
    IsUnitaryDigraph (lineDigraph D) ↔ Eulerian D :=
  ⟨eulerian_of_unitary_lineDigraph D, isUnitaryDigraph_lineDigraph_of_eulerian D⟩

theorem theorem3_eulerianComponents {V : Type} [Fintype V] [DecidableEq V]
    (D : Defs.Digraph V) [Fintype (Arc D)] [DecidableEq (Arc D)] :
    IsUnitaryDigraph (lineDigraph D) ↔ Eulerian D ∨ EulerianComponents D := by
  rw [theorem3]
  constructor
  · intro h; exact Or.inl h
  · rintro (h | h)
    · exact h
    · exact h

end Qatlib.Papers.UnitaryDigraph.MainResults.Eulerian
