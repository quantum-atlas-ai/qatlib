/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.WireComposition.CountedClusterCZ
import Qatlib.Concepts.ShadowModels.ShadowChannel.TensorPauliRecords
import Qatlib.Concepts.ClusterPatterns.AdaptiveEuler.ClusterSequenceInstrument

/-!
# Logical gates for local cluster networks

`ClusterNetworkGate` describes words built from one-wire `clusterJ` gates and controlled-Z
gates. `networkLegal` imposes unit-norm wire phases and distinct controlled-Z endpoints, while
`networkCounts` records the two gate counts.

`networkGateMatrix` and `networkLogicalMatrix` give the logical matrix semantics used for
cluster-state computation [RaussendorfBriegel2001]. The module proves endpoint symmetry for
controlled-Z gates and unitarity of legal words.

## Main statements

* `networkWireGate_unitary`: unitarity of a wire gate with a unit-norm phase.
* `networkCzGate_comm`: symmetry of controlled-Z endpoints.
* `networkLogicalMatrix_unitary`: unitarity of every legal network word.

## References

* [Raussendorf and Briegel, 2001][RaussendorfBriegel2001]
-/

open Qatlib.Foundations.PureStateMath
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Matrix
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open scoped ComplexOrder
open scoped Classical

set_option linter.unusedSectionVars false

open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.ClusterPatterns.WireComposition
open Qatlib.Concepts.PauliClifford.ExactRank

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

/-- A network gate is either a wire index with a complex phase or a pair of controlled-Z wire
indices. -/
abbrev ClusterNetworkGate (n : ℕ) := Sum (Fin n × ℂ) (Fin n × Fin n)

/-- A network word is legal when all wire phases have norm one and all controlled-Z endpoints
are distinct. -/
def networkLegal {n : ℕ} (gs : List (ClusterNetworkGate n)) : Prop :=
  ∀ g ∈ gs, match g with
    | .inl (_, ζ) => ‖ζ‖ = 1
    | .inr (i, j) => i ≠ j

/-- Counts the wire gates and controlled-Z gates in a network word, in that order. -/
def networkCounts {n : ℕ} : List (ClusterNetworkGate n) → ℕ × ℕ
  | [] => (0, 0)
  | .inl _ :: gs => ((networkCounts gs).1 + 1, (networkCounts gs).2)
  | .inr _ :: gs => ((networkCounts gs).1, (networkCounts gs).2 + 1)

/-- The register-indexed tensor gate applying `clusterJ ζ` on wire `i` and the identity on every
other wire. -/
noncomputable def networkWireGateB {n : ℕ} (i : Fin n) (ζ : ℂ) : Matrix (Reg n) (Reg n) ℂ :=
  pauliProductDensity (fun j => if j = i then clusterJ ζ else 1)

/-- The finite-indexed gate applying `clusterJ ζ` on wire `i` of an `n`-qubit register. -/
noncomputable def networkWireGate {n : ℕ} (i : Fin n) (ζ : ℂ) : Operator (2 ^ n) :=
  tensorPauliWireGate n i (clusterJ ζ)

/-- The register-indexed wire gate is obtained by relabeling the finite-indexed wire gate along
the inverse bit-vector equivalence. -/
theorem networkWireGateB_eq {n : ℕ} (i : Fin n) (ζ : ℂ) :
    networkWireGateB i ζ = relabelGate (bitVecEquiv n).symm (networkWireGate i ζ) := by
  have h : networkWireGate i ζ = relabelGate (bitVecEquiv n) (networkWireGateB i ζ) := rfl
  rw [h, relabelGate_relabelGate]

/-- The diagonal register gate with phase minus one when the bits at `i` and `j` are both true
and phase one otherwise. -/
noncomputable def networkCzGateB {n : ℕ} (i j : Fin n) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.diagonal fun x => if x i && x j then (-1 : ℂ) else 1

/-- The finite-indexed form of the register diagonal gate `networkCzGateB i j`. -/
noncomputable def networkCzGate {n : ℕ} (i j : Fin n) : Operator (2 ^ n) :=
  relabelGate (bitVecEquiv n) (networkCzGateB i j)

/-- The register-indexed controlled-Z phase gate is unitary for any pair of wire indices. -/
theorem networkCzGateB_unitary {n : ℕ} (i j : Fin n) :
    networkCzGateB i j ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  unfold networkCzGateB
  refine diagonal_mem_unitaryGroup _ fun x => ?_
  cases x i <;> cases x j <;> simp

/-- A wire gate is unitary when its complex phase has norm one. -/
theorem networkWireGate_unitary {n : ℕ} (i : Fin n) (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    networkWireGate i ζ ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
  tensorPauliWireGate_unitary n i _ (clusterJ_unitary hζ)

/-- The finite-indexed controlled-Z phase gate is unitary for any pair of wire indices. -/
theorem networkCzGate_unitary {n : ℕ} (i j : Fin n) :
    networkCzGate i j ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
  teleportRelabelGate_mem_unitaryGroup (networkCzGateB_unitary i j) _

/-- Exchanging the two endpoints leaves the register-indexed controlled-Z gate unchanged. -/
theorem networkCzGateB_comm {n : ℕ} (i j : Fin n) :
    networkCzGateB i j = networkCzGateB j i := by
  ext x y
  simp only [networkCzGateB, Matrix.diagonal_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [Bool.and_comm]
  · rw [if_neg hxy, if_neg hxy]

/-- Exchanging the two endpoints leaves the finite-indexed controlled-Z gate unchanged. -/
theorem networkCzGate_comm {n : ℕ} (i j : Fin n) :
    networkCzGate i j = networkCzGate j i := by
  rw [networkCzGate, networkCzGate, networkCzGateB_comm]

/-- The logical matrix associated with a wire or controlled-Z network gate. -/
noncomputable def networkGateMatrix {n : ℕ} : ClusterNetworkGate n → Operator (2 ^ n)
  | .inl (i, ζ) => networkWireGate i ζ
  | .inr (i, j) => networkCzGate i j

/-- The logical matrix of a network word, with the head gate applied first and the empty word
represented by the identity. -/
noncomputable def networkLogicalMatrix {n : ℕ} : List (ClusterNetworkGate n) → Operator (2 ^ n)
  | [] => 1
  | g :: gs => networkLogicalMatrix gs * networkGateMatrix g

/-- The logical matrix of a legal singleton network gate is unitary. -/
theorem networkGateMatrix_unitary {n : ℕ} (g : ClusterNetworkGate n)
    (hg : networkLegal [g]) : networkGateMatrix g ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  cases g with
  | inl p =>
    obtain ⟨i, ζ⟩ := p
    exact networkWireGate_unitary i ζ (hg _ List.mem_cons_self)
  | inr p =>
    obtain ⟨i, j⟩ := p
    exact networkCzGate_unitary i j

/-- The logical matrix of a legal network word is unitary. -/
theorem networkLogicalMatrix_unitary {n : ℕ} (gs : List (ClusterNetworkGate n))
    (hgs : networkLegal gs) : networkLogicalMatrix gs ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  induction gs with
  | nil => exact Submonoid.one_mem _
  | cons g gs ih =>
    show networkLogicalMatrix gs * networkGateMatrix g ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ
    exact Submonoid.mul_mem _
      (ih fun g' hg' => hgs g' (List.mem_cons_of_mem g hg'))
      (networkGateMatrix_unitary g (fun g' hg' => by
        rw [List.mem_singleton] at hg'
        subst hg'
        exact hgs _ List.mem_cons_self))
end Qatlib.Concepts.MbqcFlow.FlowDecision
