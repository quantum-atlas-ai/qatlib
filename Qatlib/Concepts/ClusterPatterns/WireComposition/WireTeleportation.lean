/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.WireComposition.CountedClusterWire

/-!
# Cluster wire teleportation

This module packages the circuit and instrument descriptions of cluster wire teleportation. For
a unit-modulus phase, `wire_teleportation_actual` identifies the actual branches with the
abstract instrument and gives a well-formed program with two leaves.

The corrected conditional output is conjugation by `clusterJ ζ` for either outcome, each
occurring with probability one half on a density operator. The feedback results give injective
one-bit and two-bit encodings for one and two wire steps, respectively, following the
propagation setting of [RaussendorfBriegel2000].

## Main statements

* `wire_teleportation_actual`: identifies actual and abstract branches and indexes the leaves.
* `wire_byproduct_law`: gives uniform outcome probabilities and the corrected conditional state.
* `wire_classical_feedback_bits`: records message lengths, injectivity, and two-step leaf
  indexing.

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
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.ClusterPatterns.WireComposition

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.ClusterPatterns.WireComposition

open Matrix Qatlib

/-- For a unit-modulus phase, the actual wire branches equal the abstract instrument branches,
and the program is well formed with two leaves indexed bijectively by Boolean outcomes. This
formalizes one-step wire propagation from [RaussendorfBriegel2000]. -/
theorem wire_teleportation_actual (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    (∀ b : Bool, clusterWireActualBranchMap ζ b = (clusterWireInstrument ζ hζ).branch b) ∧
    observedWellFormed (clusterWireProgram ζ) ∧
    observedLeafCount (clusterWireProgram ζ) = 2 ∧
    Function.Bijective (clusterWireLeaf ζ) := by
  obtain ⟨hwf, hcount, _hleaf, hbij⟩ := cluster_wire_actual_counts ζ hζ
  exact ⟨cluster_wire_actual_program_bridge ζ hζ, hwf, hcount, hbij⟩

/-- For a density operator and a unit-modulus phase, each wire outcome has probability one half
and its corrected conditional state is conjugation by `clusterJ ζ`. This is the
outcome-independent propagation law of [RaussendorfBriegel2000]. -/
theorem wire_byproduct_law (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    ∀ (ρ : Operator 2) (_hρ : IsDensityOperator ρ) (b : Bool),
      instrumentProb (clusterWireInstrument ζ hζ) ρ b = 1 / 2 ∧
        (∀ h : 0 < instrumentProb (clusterWireInstrument ζ hζ) ρ b,
          (clusterWireInstrument ζ hζ).conditionalState ρ b h = conjBranch (clusterJ ζ) ρ) :=
  cluster_wire_conditional_output ζ hζ

/-- One-step and two-step feedback messages encode their outcomes injectively using one and two
bits, respectively, and two-step outcomes index all circuit leaves bijectively. These counts
describe classical feedback for wire propagation in [RaussendorfBriegel2000]. -/
theorem wire_classical_feedback_bits :
    (∀ b : Bool, (clusterWireMessage b).length = 1) ∧
    Function.Injective clusterWireMessage ∧
    (∀ a b : Bool, (clusterTwoMessage a b).length = 2) ∧
    Function.Injective (fun o : Bool × Bool => clusterTwoMessage o.1 o.2) ∧
    (∀ ζ ξ : ℂ, Function.Bijective (fun o : Bool × Bool => clusterTwoLeaf ζ ξ o.1 o.2)) :=
  cluster_wire_classical_feedback_cost

end Qatlib.Concepts.ClusterPatterns.WireComposition
