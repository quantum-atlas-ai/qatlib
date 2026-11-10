/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.WireComposition.CountedClusterCZ
import Qatlib.Concepts.ShadowModels.ShadowChannel.TensorPauliRecords
import Qatlib.Concepts.ClusterPatterns.AdaptiveEuler.ClusterSequenceInstrument
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

abbrev ClusterNetworkGate (n : ℕ) := Sum (Fin n × ℂ) (Fin n × Fin n)

def networkLegal {n : ℕ} (gs : List (ClusterNetworkGate n)) : Prop :=
  ∀ g ∈ gs, match g with
    | .inl (_, ζ) => ‖ζ‖ = 1
    | .inr (i, j) => i ≠ j

def networkCounts {n : ℕ} : List (ClusterNetworkGate n) → ℕ × ℕ
  | [] => (0, 0)
  | .inl _ :: gs => ((networkCounts gs).1 + 1, (networkCounts gs).2)
  | .inr _ :: gs => ((networkCounts gs).1, (networkCounts gs).2 + 1)

noncomputable def networkWireGateB {n : ℕ} (i : Fin n) (ζ : ℂ) : Matrix (Reg n) (Reg n) ℂ :=
  pauliProductDensity (fun j => if j = i then clusterJ ζ else 1)

noncomputable def networkWireGate {n : ℕ} (i : Fin n) (ζ : ℂ) : Operator (2 ^ n) :=
  tensorPauliWireGate n i (clusterJ ζ)

theorem networkWireGateB_eq {n : ℕ} (i : Fin n) (ζ : ℂ) :
    networkWireGateB i ζ = relabelGate (bitVecEquiv n).symm (networkWireGate i ζ) := by
  have h : networkWireGate i ζ = relabelGate (bitVecEquiv n) (networkWireGateB i ζ) := rfl
  rw [h, relabelGate_relabelGate]

noncomputable def networkCzGateB {n : ℕ} (i j : Fin n) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.diagonal fun x => if x i && x j then (-1 : ℂ) else 1

noncomputable def networkCzGate {n : ℕ} (i j : Fin n) : Operator (2 ^ n) :=
  relabelGate (bitVecEquiv n) (networkCzGateB i j)

theorem networkCzGateB_unitary {n : ℕ} (i j : Fin n) :
    networkCzGateB i j ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  unfold networkCzGateB
  refine diagonal_mem_unitaryGroup _ fun x => ?_
  cases x i <;> cases x j <;> simp

theorem networkWireGate_unitary {n : ℕ} (i : Fin n) (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    networkWireGate i ζ ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
  tensorPauliWireGate_unitary n i _ (clusterJ_unitary hζ)

theorem networkCzGate_unitary {n : ℕ} (i j : Fin n) :
    networkCzGate i j ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
  teleportRelabelGate_mem_unitaryGroup (networkCzGateB_unitary i j) _

theorem networkCzGateB_comm {n : ℕ} (i j : Fin n) :
    networkCzGateB i j = networkCzGateB j i := by
  ext x y
  simp only [networkCzGateB, Matrix.diagonal_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [Bool.and_comm]
  · rw [if_neg hxy, if_neg hxy]

theorem networkCzGate_comm {n : ℕ} (i j : Fin n) :
    networkCzGate i j = networkCzGate j i := by
  rw [networkCzGate, networkCzGate, networkCzGateB_comm]

noncomputable def networkGateMatrix {n : ℕ} : ClusterNetworkGate n → Operator (2 ^ n)
  | .inl (i, ζ) => networkWireGate i ζ
  | .inr (i, j) => networkCzGate i j

noncomputable def networkLogicalMatrix {n : ℕ} : List (ClusterNetworkGate n) → Operator (2 ^ n)
  | [] => 1
  | g :: gs => networkLogicalMatrix gs * networkGateMatrix g

theorem networkGateMatrix_unitary {n : ℕ} (g : ClusterNetworkGate n)
    (hg : networkLegal [g]) : networkGateMatrix g ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  cases g with
  | inl p =>
    obtain ⟨i, ζ⟩ := p
    exact networkWireGate_unitary i ζ (hg _ List.mem_cons_self)
  | inr p =>
    obtain ⟨i, j⟩ := p
    exact networkCzGate_unitary i j

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
