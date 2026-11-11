/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.WireComposition.CountedClusterCNOT

/-!
# Cluster CNOT theorem interface

This module exposes the resource, channel, basis-action, and cost theorems for the counted
cluster CNOT construction. In the chosen pair convention, the second logical bit controls a flip
of the first.

Raw branches display their outcome-dependent byproducts, while corrected branches implement the
CNOT with amplitude one half. The reference-system and resource-count results connect the
physical program to the measurement-based gate construction of [RaussendorfBriegel2000].

## Main statements

* `cluster_cnot_branch_and_reference_channel`: exact branch and forgotten-channel action with
  references.
* `cluster_cnot_program_and_feedback_cost_paper`: raw and corrected gate counts and two-bit
  messages.
* `cluster_cnot_corrected_frame_paper`: corrected computational-basis branch action.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000]
-/

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

/-- The CNOT input frame is an isometry, and both the raw and corrected observed programs are
well formed. See [RaussendorfBriegel2000]. -/
theorem cluster_cnot_resource_preparation_paper :
    IsIsometry clusterCNOTInitialFrame ∧
      observedWellFormed clusterCNOTRawProgram ∧ observedWellFormed clusterCNOTProgram :=
  cluster_cnot_resource_preparation

/-- Each corrected CNOT branch is one quarter of CNOT conjugation, including arbitrary reference
extensions, and summing all reference-extended branches gives the CNOT channel. See
[RaussendorfBriegel2000]. -/
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

/-- The raw and corrected CNOT programs each have four accepting, query-free branches with two
measurements and injective two-bit messages, using seven and ten gates respectively. See
[RaussendorfBriegel2000]. -/
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

/-- The CNOT matrix sends a basis pair `(t, c)` to `(t XOR c, c)`, so the second bit controls
the first. See [RaussendorfBriegel2000]. -/
theorem cluster_cnot_basis_action_paper (x y t c : Bool) :
    clusterCNOTMat (teleportOutcomeEquiv (x, y)) (teleportOutcomeEquiv (t, c)) =
      if (x, y) = (t ^^ c, c) then (1 : ℂ) else 0 :=
  clusterCNOTMat_tele_entry x y t c

/-- The CNOT matrix preserves the target when the control is false and flips it when the control
is true. See [RaussendorfBriegel2000]. -/
theorem cluster_cnot_control_selects_flip_paper (t : Bool) :
    clusterCNOTMat (teleportOutcomeEquiv (t, false)) (teleportOutcomeEquiv (t, false)) = 1 ∧
    clusterCNOTMat (teleportOutcomeEquiv (!t, true)) (teleportOutcomeEquiv (t, true)) = 1 := by
  cases t <;> simp [clusterCNOTMat_tele_entry]

/-- A raw CNOT branch is supported on its measured pair and maps `(t, c)` to `(t XOR c XOR b,
c)` with amplitude `(-1)^(a * t) / 2`. See [RaussendorfBriegel2000]. -/
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

/-- A corrected CNOT branch is supported on its measured pair and outputs the basis pair `(t XOR
c, c)` with amplitude one half. See [RaussendorfBriegel2000]. -/
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
