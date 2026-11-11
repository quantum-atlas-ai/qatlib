/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Card
import Mathlib.Logic.Relation
import Mathlib.Data.Finset.Basic

/-!
# Digraph predicates for unitary support patterns

This module defines directed adjacency, neighborhood sets, and the predicate `IsUnitaryDigraph`
for nonzero patterns of finite complex unitary matrices. It supplies quadrangularity and
specularity predicates, line digraphs, degree-balance and cycle predicates, and path, cycle, and
Cayley examples.

The tree predicates encode absence of the corresponding cycles, and `Eulerian` and
`EulerianComponents` both encode equality of incoming and outgoing neighborhood cardinalities.
Reversal interchanges the incoming and outgoing constructions. See [Severini2003].

## Main statements

* `IsUnitaryDigraph`: Existence of a unitary matrix with exactly the given support.
* `lineDigraph`: The digraph of composable arcs.
* `reverse_reverse`: Reversing every arc twice recovers the original digraph.

## References

* [Severini, 2003][Severini2003]
-/

set_option autoImplicit false
noncomputable section

open Set

namespace Qatlib.Papers.UnitaryDigraph.MainResults.Defs

/-- A directed graph specified by a binary adjacency relation on its vertices. -/
structure Digraph (V : Type) where

  Adj : V → V → Prop

namespace Digraph

variable {V : Type}

/-- The complete digraph in which every ordered vertex pair, including each loop, is adjacent. -/
def complete (V : Type) : Digraph V := ⟨fun _ _ => True⟩

/-- The set of vertices reached by an outgoing arc from some vertex of `S`. -/
def outNbrsSet (D : Digraph V) (S : Set V) : Set V := {w | ∃ v ∈ S, D.Adj v w}

/-- The set of outgoing neighbors of a single vertex. -/
def outNbrs (D : Digraph V) (v : V) : Set V := D.outNbrsSet {v}

/-- The set of vertices with an outgoing arc to some vertex of `S`. -/
def inNbrsSet (D : Digraph V) (S : Set V) : Set V := {u | ∃ v ∈ S, D.Adj u v}

/-- The set of incoming neighbors of a single vertex. -/
def inNbrs (D : Digraph V) (v : V) : Set V := D.inNbrsSet {v}

/-- Membership in the outgoing neighborhood is equivalent to adjacency from the given vertex. -/
@[simp] theorem mem_outNbrs {D : Digraph V} {v w : V} : w ∈ D.outNbrs v ↔ D.Adj v w := by
  simp [outNbrs, outNbrsSet]

/-- Membership in the incoming neighborhood is equivalent to adjacency to the given vertex. -/
@[simp] theorem mem_inNbrs {D : Digraph V} {v u : V} : u ∈ D.inNbrs v ↔ D.Adj u v := by
  simp [inNbrs, inNbrsSet]

/-- The outgoing neighborhood is the set of vertices adjacent from the given vertex. -/
theorem outNbrs_eq (D : Digraph V) (v : V) : D.outNbrs v = {w | D.Adj v w} := by
  ext w; simp

/-- The incoming neighborhood is the set of vertices adjacent to the given vertex. -/
theorem inNbrs_eq (D : Digraph V) (v : V) : D.inNbrs v = {u | D.Adj u v} := by
  ext u; simp

/-- The union of outgoing neighborhoods of vertices in `S` other than `i`. -/
def outNbrsOthers (D : Digraph V) (S : Set V) (i : V) : Set V :=
  ⋃ j ∈ S, ⋃ (_ : j ≠ i), D.outNbrs j

/-- The union of incoming neighborhoods of vertices in `S` other than `i`. -/
def inNbrsOthers (D : Digraph V) (S : Set V) (i : V) : Set V :=
  ⋃ j ∈ S, ⋃ (_ : j ≠ i), D.inNbrs j

/-- An outgoing neighbor of a vertex in `S` distinct from `i` belongs to `outNbrsOthers S i`. -/
theorem mem_outNbrsOthers {D : Digraph V} {S : Set V} {i j c : V}
    (hjS : j ∈ S) (hjne : j ≠ i) (hc : c ∈ D.outNbrs j) : c ∈ D.outNbrsOthers S i := by
  simp only [outNbrsOthers, Set.mem_iUnion, exists_prop]
  exact ⟨j, hjS, hjne, hc⟩

/-- An incoming neighbor of a vertex in `S` distinct from `i` belongs to `inNbrsOthers S i`. -/
theorem mem_inNbrsOthers {D : Digraph V} {S : Set V} {i j c : V}
    (hjS : j ∈ S) (hjne : j ≠ i) (hc : c ∈ D.inNbrs j) : c ∈ D.inNbrsOthers S i := by
  simp only [inNbrsOthers, Set.mem_iUnion, exists_prop]
  exact ⟨j, hjS, hjne, hc⟩

end Digraph

/-- The property that a finite digraph is exactly the nonzero-entry pattern of a complex unitary
matrix. -/
def IsUnitaryDigraph {V : Type} [Fintype V] [DecidableEq V] (D : Digraph V) : Prop :=
  ∃ U : Matrix V V ℂ, U ∈ Matrix.unitaryGroup V ℂ ∧ ∀ i j, U i j ≠ 0 ↔ D.Adj i j

/-- The property that distinct vertices have neither an outgoing-neighbor intersection nor an
incoming-neighbor intersection of cardinality one. -/
def Quadrangular {V : Type} (D : Digraph V) : Prop :=
  ∀ i j : V, i ≠ j →
    (D.outNbrs i ∩ D.outNbrs j).ncard ≠ 1 ∧ (D.inNbrs i ∩ D.inNbrs j).ncard ≠ 1

/-- The absence of a vertex set `S` whose distinct pairs have outgoing intersections contained
in a set `T` and incoming intersections contained in a set `T′`, each of cardinality smaller
than `S`, while every vertex shares a neighbor with another vertex of `S` in each direction. -/
def StronglyQuadrangular {V : Type} (D : Digraph V) : Prop :=
  ¬ ∃ (S T T' : Set V),
      T.ncard < S.ncard ∧ T'.ncard < S.ncard ∧
      (∀ i ∈ S, (D.outNbrs i ∩ D.outNbrsOthers S i).Nonempty) ∧
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → D.outNbrs i ∩ D.outNbrs j ⊆ T) ∧
      (∀ i ∈ S, (D.inNbrs i ∩ D.inNbrsOthers S i).Nonempty) ∧
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → D.inNbrs i ∩ D.inNbrs j ⊆ T')

/-- The absence of a vertex set `S` in which every vertex shares an outgoing neighbor with
another member and all distinct-pair outgoing intersections lie in a set of cardinality
smaller than `S`. -/
def OutStronglyQuadrangular {V : Type} (D : Digraph V) : Prop :=
  ¬ ∃ (S T : Set V),
      T.ncard < S.ncard ∧
      (∀ i ∈ S, (D.outNbrs i ∩ D.outNbrsOthers S i).Nonempty) ∧
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → D.outNbrs i ∩ D.outNbrs j ⊆ T)

/-- The property that the outgoing neighborhoods of distinct vertices never intersect in exactly
one vertex. -/
def OutQuadrangular {V : Type} (D : Digraph V) : Prop :=
  ∀ i j : V, i ≠ j → (D.outNbrs i ∩ D.outNbrs j).ncard ≠ 1

/-- The absence of a vertex set `S` in which every vertex shares an incoming neighbor with
another member and all distinct-pair incoming intersections lie in a set of cardinality
smaller than `S`. -/
def InStronglyQuadrangular {V : Type} (D : Digraph V) : Prop :=
  ¬ ∃ (S T : Set V),
      T.ncard < S.ncard ∧
      (∀ i ∈ S, (D.inNbrs i ∩ D.inNbrsOthers S i).Nonempty) ∧
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → D.inNbrs i ∩ D.inNbrs j ⊆ T)

/-- The property that overlapping outgoing neighborhoods of distinct vertices coincide, and
likewise for incoming neighborhoods. -/
def Specular {V : Type} (D : Digraph V) : Prop :=
  (∀ i j : V, i ≠ j → (D.outNbrs i ∩ D.outNbrs j).Nonempty → D.outNbrs i = D.outNbrs j) ∧
  (∀ i j : V, i ≠ j → (D.inNbrs i ∩ D.inNbrs j).Nonempty → D.inNbrs i = D.inNbrs j)

/-- The existence of separate vertex equivalences for row and column indices that preserve the
adjacency pattern. -/
def PermEquivalentTo {V W : Type} (D : Digraph V) (D' : Digraph W) : Prop :=
  ∃ (σ τ : V ≃ W), ∀ i j, D'.Adj (σ i) (τ j) ↔ D.Adj i j

/-- The existence of a single vertex equivalence preserving adjacency in both directions. -/
def Isomorphic {V W : Type} (D : Digraph V) (D' : Digraph W) : Prop :=
  ∃ e : V ≃ W, ∀ i j, D.Adj i j ↔ D'.Adj (e i) (e j)

/-- The type of ordered adjacent vertex pairs, regarded as arcs of the digraph. -/
def Arc {V : Type} (D : Digraph V) := { p : V × V // D.Adj p.1 p.2 }

/-- The digraph on arcs in which an arc is adjacent to another when its target equals the other
arc’s source. -/
def lineDigraph {V : Type} (D : Digraph V) : Digraph (Arc D) :=
  ⟨fun a b => a.1.2 = b.1.1⟩

/-- The property of being isomorphic to the line digraph of some digraph. -/
def IsLineDigraph {V : Type} (D : Digraph V) : Prop :=
  ∃ (W : Type) (D₀ : Digraph W), Isomorphic D (lineDigraph D₀)

/-- The cyclic successor of an index in `Fin n`, computed modulo positive `n`. -/
def next {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩

/-- The existence of a positive-length directed cycle with injectively indexed vertices. -/
def HasDirectedCycle {V : Type} (D : Digraph V) : Prop :=
  ∃ (n : ℕ) (hn : 0 < n) (c : Fin n → V),
    Function.Injective c ∧ ∀ i : Fin n, D.Adj (c i) (c (next hn i))

/-- Adjacency in at least one direction between the two specified vertices. -/
def symmAdj {V : Type} (D : Digraph V) (a b : V) : Prop := D.Adj a b ∨ D.Adj b a

/-- The existence of a cycle of length at least three with injectively indexed vertices in the
symmetrized adjacency relation. -/
def HasUndirectedCycle {V : Type} (D : Digraph V) : Prop :=
  ∃ (n : ℕ) (hn : 2 < n) (c : Fin n → V),
    Function.Injective c ∧
      ∀ i : Fin n, symmAdj D (c i) (c (next (Nat.lt_trans (by decide : (0:ℕ) < 2) hn) i))

/-- The predicate that the digraph has no directed cycle. -/
def IsDirectedTree {V : Type} (D : Digraph V) : Prop := ¬ HasDirectedCycle D

/-- The predicate that the symmetrized adjacency relation has no cycle of length at least three. -/
def IsTree {V : Type} (D : Digraph V) : Prop := ¬ HasUndirectedCycle D

/-- Reachability by a finite directed path, including the path of length zero. -/
def Reachable {V : Type} (D : Digraph V) (a b : V) : Prop := Relation.ReflTransGen D.Adj a b

/-- The property that every vertex is reachable from every other vertex. -/
def StronglyConnected {V : Type} (D : Digraph V) : Prop := ∀ a b, Reachable D a b

/-- The degree-balance predicate requiring incoming and outgoing neighborhood cardinalities to
agree at every vertex. -/
def Eulerian {V : Type} (D : Digraph V) : Prop :=
  ∀ v : V, (D.inNbrs v).ncard = (D.outNbrs v).ncard

/-- The predicate requiring equality of incoming and outgoing neighborhood cardinalities at each
vertex. -/
def EulerianComponents {V : Type} (D : Digraph V) : Prop :=
  ∀ v : V, (D.inNbrs v).ncard = (D.outNbrs v).ncard

/-- The existence of a positive-length directed cycle whose vertex indexing is bijective onto
all vertices. -/
def Hamiltonian {V : Type} (D : Digraph V) : Prop :=
  ∃ (n : ℕ) (hn : 0 < n) (c : Fin n → V),
    Function.Bijective c ∧ ∀ i : Fin n, D.Adj (c i) (c (next hn i))

/-- The bidirected path on `Fin n`, with adjacency between consecutive indices. -/
def nPath (n : ℕ) : Digraph (Fin n) :=
  ⟨fun i j => i.val + 1 = j.val ∨ j.val + 1 = i.val⟩

/-- The bidirected path on `Fin n` with a loop at every vertex. -/
def nPathLoops (n : ℕ) : Digraph (Fin n) :=
  ⟨fun i j => i = j ∨ i.val + 1 = j.val ∨ j.val + 1 = i.val⟩

/-- The bidirected cycle on `Fin n`, with adjacency given by cyclic succession in either
direction. -/
def nCycle (n : ℕ) : Digraph (Fin n) :=
  ⟨fun i j => (i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val⟩

/-- The directed cycle on `Fin n`, with an arc from each index to its successor modulo `n`. -/
def directedNCycle (n : ℕ) : Digraph (Fin n) :=
  ⟨fun i j => (i.val + 1) % n = j.val⟩

/-- The Cayley digraph with an arc from `g` to `g * s` for each `s` in the finite set `S`. -/
def CayleyDigraph (G : Type) [Mul G] (S : Finset G) : Digraph G :=
  ⟨fun g h => ∃ s ∈ S, g * s = h⟩

end Qatlib.Papers.UnitaryDigraph.MainResults.Defs

namespace Qatlib.Papers.UnitaryDigraph.MainResults.Defs

namespace Digraph

/-- The digraph obtained by reversing every arc. -/
def reverse {V : Type} (D : Digraph V) : Digraph V := ⟨fun a b => D.Adj b a⟩

/-- Adjacency in the reversed digraph is adjacency in the original digraph with the arguments
exchanged. -/
@[simp] theorem reverse_adj {V : Type} (D : Digraph V) (a b : V) :
    (reverse D).Adj a b ↔ D.Adj b a := Iff.rfl

/-- The outgoing neighborhood in the reversed digraph equals the original incoming neighborhood. -/
@[simp] theorem reverse_outNbrs {V : Type} (D : Digraph V) (v : V) :
    (reverse D).outNbrs v = D.inNbrs v := rfl

/-- The incoming neighborhood in the reversed digraph equals the original outgoing neighborhood. -/
@[simp] theorem reverse_inNbrs {V : Type} (D : Digraph V) (v : V) :
    (reverse D).inNbrs v = D.outNbrs v := rfl

/-- Reversal turns the union of other vertices’ outgoing neighborhoods into the corresponding
union of incoming neighborhoods. -/
@[simp] theorem reverse_outNbrsOthers {V : Type} (D : Digraph V) (S : Set V) (i : V) :
    (reverse D).outNbrsOthers S i = D.inNbrsOthers S i := rfl

/-- Reversal turns the union of other vertices’ incoming neighborhoods into the corresponding
union of outgoing neighborhoods. -/
@[simp] theorem reverse_inNbrsOthers {V : Type} (D : Digraph V) (S : Set V) (i : V) :
    (reverse D).inNbrsOthers S i = D.outNbrsOthers S i := rfl

/-- Reversing a digraph twice gives the original digraph. -/
@[simp] theorem reverse_reverse {V : Type} (D : Digraph V) : reverse (reverse D) = D := rfl

end Digraph

end Qatlib.Papers.UnitaryDigraph.MainResults.Defs
