/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.WireComposition.CountedClusterWire
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.ClusterPatterns.WireComposition

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.ClusterPatterns.WireComposition

open Matrix Qatlib

theorem wire_teleportation_actual (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    (∀ b : Bool, clusterWireActualBranchMap ζ b = (clusterWireInstrument ζ hζ).branch b) ∧
    observedWellFormed (clusterWireProgram ζ) ∧
    observedLeafCount (clusterWireProgram ζ) = 2 ∧
    Function.Bijective (clusterWireLeaf ζ) := by
  obtain ⟨hwf, hcount, _hleaf, hbij⟩ := cluster_wire_actual_counts ζ hζ
  exact ⟨cluster_wire_actual_program_bridge ζ hζ, hwf, hcount, hbij⟩

theorem wire_byproduct_law (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    ∀ (ρ : Operator 2) (_hρ : IsDensityOperator ρ) (b : Bool),
      instrumentProb (clusterWireInstrument ζ hζ) ρ b = 1 / 2 ∧
        (∀ h : 0 < instrumentProb (clusterWireInstrument ζ hζ) ρ b,
          (clusterWireInstrument ζ hζ).conditionalState ρ b h = conjBranch (clusterJ ζ) ρ) :=
  cluster_wire_conditional_output ζ hζ

theorem wire_classical_feedback_bits :
    (∀ b : Bool, (clusterWireMessage b).length = 1) ∧
    Function.Injective clusterWireMessage ∧
    (∀ a b : Bool, (clusterTwoMessage a b).length = 2) ∧
    Function.Injective (fun o : Bool × Bool => clusterTwoMessage o.1 o.2) ∧
    (∀ ζ ξ : ℂ, Function.Bijective (fun o : Bool × Bool => clusterTwoLeaf ζ ξ o.1 o.2)) :=
  cluster_wire_classical_feedback_cost

end Qatlib.Concepts.ClusterPatterns.WireComposition
