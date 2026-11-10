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

set_option autoImplicit false
noncomputable section

open Set

namespace Qatlib.Papers.UnitaryDigraph.MainResults.Defs

structure Digraph (V : Type) where

  Adj : V → V → Prop

namespace Digraph

variable {V : Type}

def complete (V : Type) : Digraph V := ⟨fun _ _ => True⟩

def outNbrsSet (D : Digraph V) (S : Set V) : Set V := {w | ∃ v ∈ S, D.Adj v w}

def outNbrs (D : Digraph V) (v : V) : Set V := D.outNbrsSet {v}

def inNbrsSet (D : Digraph V) (S : Set V) : Set V := {u | ∃ v ∈ S, D.Adj u v}

def inNbrs (D : Digraph V) (v : V) : Set V := D.inNbrsSet {v}

@[simp] theorem mem_outNbrs {D : Digraph V} {v w : V} : w ∈ D.outNbrs v ↔ D.Adj v w := by
  simp [outNbrs, outNbrsSet]

@[simp] theorem mem_inNbrs {D : Digraph V} {v u : V} : u ∈ D.inNbrs v ↔ D.Adj u v := by
  simp [inNbrs, inNbrsSet]

theorem outNbrs_eq (D : Digraph V) (v : V) : D.outNbrs v = {w | D.Adj v w} := by
  ext w; simp

theorem inNbrs_eq (D : Digraph V) (v : V) : D.inNbrs v = {u | D.Adj u v} := by
  ext u; simp

def outNbrsOthers (D : Digraph V) (S : Set V) (i : V) : Set V :=
  ⋃ j ∈ S, ⋃ (_ : j ≠ i), D.outNbrs j

def inNbrsOthers (D : Digraph V) (S : Set V) (i : V) : Set V :=
  ⋃ j ∈ S, ⋃ (_ : j ≠ i), D.inNbrs j

theorem mem_outNbrsOthers {D : Digraph V} {S : Set V} {i j c : V}
    (hjS : j ∈ S) (hjne : j ≠ i) (hc : c ∈ D.outNbrs j) : c ∈ D.outNbrsOthers S i := by
  simp only [outNbrsOthers, Set.mem_iUnion, exists_prop]
  exact ⟨j, hjS, hjne, hc⟩

theorem mem_inNbrsOthers {D : Digraph V} {S : Set V} {i j c : V}
    (hjS : j ∈ S) (hjne : j ≠ i) (hc : c ∈ D.inNbrs j) : c ∈ D.inNbrsOthers S i := by
  simp only [inNbrsOthers, Set.mem_iUnion, exists_prop]
  exact ⟨j, hjS, hjne, hc⟩

end Digraph

def IsUnitaryDigraph {V : Type} [Fintype V] [DecidableEq V] (D : Digraph V) : Prop :=
  ∃ U : Matrix V V ℂ, U ∈ Matrix.unitaryGroup V ℂ ∧ ∀ i j, U i j ≠ 0 ↔ D.Adj i j

def Quadrangular {V : Type} (D : Digraph V) : Prop :=
  ∀ i j : V, i ≠ j →
    (D.outNbrs i ∩ D.outNbrs j).ncard ≠ 1 ∧ (D.inNbrs i ∩ D.inNbrs j).ncard ≠ 1

def StronglyQuadrangular {V : Type} (D : Digraph V) : Prop :=
  ¬ ∃ (S T T' : Set V),
      T.ncard < S.ncard ∧ T'.ncard < S.ncard ∧
      (∀ i ∈ S, (D.outNbrs i ∩ D.outNbrsOthers S i).Nonempty) ∧
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → D.outNbrs i ∩ D.outNbrs j ⊆ T) ∧
      (∀ i ∈ S, (D.inNbrs i ∩ D.inNbrsOthers S i).Nonempty) ∧
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → D.inNbrs i ∩ D.inNbrs j ⊆ T')

def OutStronglyQuadrangular {V : Type} (D : Digraph V) : Prop :=
  ¬ ∃ (S T : Set V),
      T.ncard < S.ncard ∧
      (∀ i ∈ S, (D.outNbrs i ∩ D.outNbrsOthers S i).Nonempty) ∧
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → D.outNbrs i ∩ D.outNbrs j ⊆ T)

def OutQuadrangular {V : Type} (D : Digraph V) : Prop :=
  ∀ i j : V, i ≠ j → (D.outNbrs i ∩ D.outNbrs j).ncard ≠ 1

def InStronglyQuadrangular {V : Type} (D : Digraph V) : Prop :=
  ¬ ∃ (S T : Set V),
      T.ncard < S.ncard ∧
      (∀ i ∈ S, (D.inNbrs i ∩ D.inNbrsOthers S i).Nonempty) ∧
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → D.inNbrs i ∩ D.inNbrs j ⊆ T)

def Specular {V : Type} (D : Digraph V) : Prop :=
  (∀ i j : V, i ≠ j → (D.outNbrs i ∩ D.outNbrs j).Nonempty → D.outNbrs i = D.outNbrs j) ∧
  (∀ i j : V, i ≠ j → (D.inNbrs i ∩ D.inNbrs j).Nonempty → D.inNbrs i = D.inNbrs j)

def PermEquivalentTo {V W : Type} (D : Digraph V) (D' : Digraph W) : Prop :=
  ∃ (σ τ : V ≃ W), ∀ i j, D'.Adj (σ i) (τ j) ↔ D.Adj i j

def Isomorphic {V W : Type} (D : Digraph V) (D' : Digraph W) : Prop :=
  ∃ e : V ≃ W, ∀ i j, D.Adj i j ↔ D'.Adj (e i) (e j)

def Arc {V : Type} (D : Digraph V) := { p : V × V // D.Adj p.1 p.2 }

def lineDigraph {V : Type} (D : Digraph V) : Digraph (Arc D) :=
  ⟨fun a b => a.1.2 = b.1.1⟩

def IsLineDigraph {V : Type} (D : Digraph V) : Prop :=
  ∃ (W : Type) (D₀ : Digraph W), Isomorphic D (lineDigraph D₀)

def next {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩

def HasDirectedCycle {V : Type} (D : Digraph V) : Prop :=
  ∃ (n : ℕ) (hn : 0 < n) (c : Fin n → V),
    Function.Injective c ∧ ∀ i : Fin n, D.Adj (c i) (c (next hn i))

def symmAdj {V : Type} (D : Digraph V) (a b : V) : Prop := D.Adj a b ∨ D.Adj b a

def HasUndirectedCycle {V : Type} (D : Digraph V) : Prop :=
  ∃ (n : ℕ) (hn : 2 < n) (c : Fin n → V),
    Function.Injective c ∧
      ∀ i : Fin n, symmAdj D (c i) (c (next (Nat.lt_trans (by decide : (0:ℕ) < 2) hn) i))

def IsDirectedTree {V : Type} (D : Digraph V) : Prop := ¬ HasDirectedCycle D

def IsTree {V : Type} (D : Digraph V) : Prop := ¬ HasUndirectedCycle D

def Reachable {V : Type} (D : Digraph V) (a b : V) : Prop := Relation.ReflTransGen D.Adj a b

def StronglyConnected {V : Type} (D : Digraph V) : Prop := ∀ a b, Reachable D a b

def Eulerian {V : Type} (D : Digraph V) : Prop :=
  ∀ v : V, (D.inNbrs v).ncard = (D.outNbrs v).ncard

def EulerianComponents {V : Type} (D : Digraph V) : Prop :=
  ∀ v : V, (D.inNbrs v).ncard = (D.outNbrs v).ncard

def Hamiltonian {V : Type} (D : Digraph V) : Prop :=
  ∃ (n : ℕ) (hn : 0 < n) (c : Fin n → V),
    Function.Bijective c ∧ ∀ i : Fin n, D.Adj (c i) (c (next hn i))

def nPath (n : ℕ) : Digraph (Fin n) :=
  ⟨fun i j => i.val + 1 = j.val ∨ j.val + 1 = i.val⟩

def nPathLoops (n : ℕ) : Digraph (Fin n) :=
  ⟨fun i j => i = j ∨ i.val + 1 = j.val ∨ j.val + 1 = i.val⟩

def nCycle (n : ℕ) : Digraph (Fin n) :=
  ⟨fun i j => (i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val⟩

def directedNCycle (n : ℕ) : Digraph (Fin n) :=
  ⟨fun i j => (i.val + 1) % n = j.val⟩

def CayleyDigraph (G : Type) [Mul G] (S : Finset G) : Digraph G :=
  ⟨fun g h => ∃ s ∈ S, g * s = h⟩

end Qatlib.Papers.UnitaryDigraph.MainResults.Defs

namespace Qatlib.Papers.UnitaryDigraph.MainResults.Defs

namespace Digraph

def reverse {V : Type} (D : Digraph V) : Digraph V := ⟨fun a b => D.Adj b a⟩

@[simp] theorem reverse_adj {V : Type} (D : Digraph V) (a b : V) :
    (reverse D).Adj a b ↔ D.Adj b a := Iff.rfl

@[simp] theorem reverse_outNbrs {V : Type} (D : Digraph V) (v : V) :
    (reverse D).outNbrs v = D.inNbrs v := rfl

@[simp] theorem reverse_inNbrs {V : Type} (D : Digraph V) (v : V) :
    (reverse D).inNbrs v = D.outNbrs v := rfl

@[simp] theorem reverse_outNbrsOthers {V : Type} (D : Digraph V) (S : Set V) (i : V) :
    (reverse D).outNbrsOthers S i = D.inNbrsOthers S i := rfl

@[simp] theorem reverse_inNbrsOthers {V : Type} (D : Digraph V) (S : Set V) (i : V) :
    (reverse D).inNbrsOthers S i = D.outNbrsOthers S i := rfl

@[simp] theorem reverse_reverse {V : Type} (D : Digraph V) : reverse (reverse D) = D := rfl

end Digraph

end Qatlib.Papers.UnitaryDigraph.MainResults.Defs
