/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.WireComposition.CountedClusterCNOT
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.ClusterPatterns.WireComposition

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.ClusterPatterns.WireComposition

open Matrix Qatlib

theorem cluster_cnot_resource_preparation_paper :
    IsIsometry clusterCNOTInitialFrame ∧
      observedWellFormed clusterCNOTRawProgram ∧ observedWellFormed clusterCNOTProgram :=
  cluster_cnot_resource_preparation

theorem cluster_cnot_branch_and_reference_channel :
    ∀ a b : Bool, ∀ ρ : Operator 4,
      clusterCNOTActualBranchMap a b ρ = (1 / 4 : ℂ) • conjBranch clusterCNOTMat ρ ∧
      ∀ (r : ℕ) (σ : Matrix (Fin 4 × Fin r) (Fin 4 × Fin r) ℂ),
        tensorLeft (clusterCNOTActualBranchMap a b) σ
          = (1 / 4 : ℂ) • (TensorGate clusterCNOTMat (1 : Operator r) * σ *
              (TensorGate clusterCNOTMat (1 : Operator r))ᴴ) ∧
        (∑ o : Bool × Bool, tensorLeft (clusterCNOTActualBranchMap o.1 o.2) σ)
          = TensorGate clusterCNOTMat (1 : Operator r) * σ *
              (TensorGate clusterCNOTMat (1 : Operator r))ᴴ :=
  cluster_cnot_actual_branch_and_reference_channel

theorem cluster_cnot_program_and_feedback_cost_paper :
    observedLeafCount clusterCNOTRawProgram = 4 ∧ observedLeafCount clusterCNOTProgram = 4 ∧
      Function.Bijective (fun o : Bool × Bool => clusterCNOTLeaf o.1 o.2) ∧
      (∀ a b : Bool,
        (observedLeaf 1 clusterCNOTRawProgram (clusterCNOTRawLeaf a b)).accepted = true ∧
        (observedLeaf 1 clusterCNOTRawProgram (clusterCNOTRawLeaf a b)).queries = 0 ∧
        (observedLeaf 1 clusterCNOTRawProgram (clusterCNOTRawLeaf a b)).gates = 7 ∧
        (observedLeaf 1 clusterCNOTRawProgram (clusterCNOTRawLeaf a b)).measurements = 2 ∧
        (observedLeaf 1 clusterCNOTRawProgram (clusterCNOTRawLeaf a b)).outcomes
          = [(2, (boolEquivFin2 a).val), (2, (boolEquivFin2 b).val)]) ∧
      (∀ a b : Bool,
        (observedLeaf 1 clusterCNOTProgram (clusterCNOTLeaf a b)).accepted = true ∧
        (observedLeaf 1 clusterCNOTProgram (clusterCNOTLeaf a b)).queries = 0 ∧
        (observedLeaf 1 clusterCNOTProgram (clusterCNOTLeaf a b)).gates = 10 ∧
        (observedLeaf 1 clusterCNOTProgram (clusterCNOTLeaf a b)).measurements = 2 ∧
        (observedLeaf 1 clusterCNOTProgram (clusterCNOTLeaf a b)).outcomes
          = [(2, (boolEquivFin2 a).val), (2, (boolEquivFin2 b).val)]) ∧
      (∀ a b : Bool, clusterCNOTMessage a b = [a, b] ∧ (clusterCNOTMessage a b).length = 2) ∧
      Function.Injective (fun o : Bool × Bool => clusterCNOTMessage o.1 o.2) :=
  cluster_cnot_actual_program_and_feedback_cost

theorem cluster_cnot_basis_action_paper (x y t c : Bool) :
    clusterCNOTMat (teleportOutcomeEquiv (x, y)) (teleportOutcomeEquiv (t, c)) =
      if (x, y) = (t ^^ c, c) then (1 : ℂ) else 0 :=
  clusterCNOTMat_tele_entry x y t c

theorem cluster_cnot_control_selects_flip_paper (t : Bool) :
    clusterCNOTMat (teleportOutcomeEquiv (t, false)) (teleportOutcomeEquiv (t, false)) = 1 ∧
    clusterCNOTMat (teleportOutcomeEquiv (!t, true)) (teleportOutcomeEquiv (t, true)) = 1 := by
  cases t <;> simp [clusterCNOTMat_tele_entry]

theorem cluster_cnot_raw_byproduct_frame_paper (a b t c : Bool) :
    ApplyGate (observedLeaf 1 clusterCNOTRawProgram (clusterCNOTRawLeaf a b)).operator
      (relabelState clusterCZRegisterEquiv
        (Qatlib.Foundations.PureStateMath.Ket ((t, false), (false, c))))
      = relabelState clusterCZRegisterEquiv
          (fun q : (Bool × Bool) × (Bool × Bool) =>
            if q.1 = (a, b) then ((if a && t then (-1 : ℂ) else 1) / 2) *
              Qatlib.Foundations.PureStateMath.Ket (t ^^ c ^^ b, c) q.2
            else 0) :=
  clusterCNOTRawLeafColumn a b t c

theorem cluster_cnot_corrected_frame_paper (a b t c : Bool) :
    ApplyGate (observedLeaf 1 clusterCNOTProgram (clusterCNOTLeaf a b)).operator
      (relabelState clusterCZRegisterEquiv
        (Qatlib.Foundations.PureStateMath.Ket ((t, false), (false, c))))
      = relabelState clusterCZRegisterEquiv
          (fun q : (Bool × Bool) × (Bool × Bool) =>
            if q.1 = (a, b) then (1 / 2 : ℂ) *
              Qatlib.Foundations.PureStateMath.Ket (t ^^ c, c) q.2
            else 0) := by
  rw [clusterCNOTLeafColumn a b t c]
  congr 1
  funext q
  rw [clusterCNOTMat_tele_entry]
  by_cases h : q.1 = (a, b) <;>
    simp [h, Qatlib.Foundations.PureStateMath.Ket]

end Qatlib.Concepts.ClusterPatterns.WireComposition
