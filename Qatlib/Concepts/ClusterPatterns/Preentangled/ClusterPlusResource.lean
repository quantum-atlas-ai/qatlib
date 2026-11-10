/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.PlusResource
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.ClusterPatterns.AdaptiveEuler
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.ClusterPatterns.WireComposition
open Qatlib.Concepts.ClusterPatterns.PlusResource

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.ClusterPatterns.Preentangled

open Matrix Qatlib
open scoped ComplexOrder

theorem cluster_plus_any_state :
    ∀ φ : QState (Fin 2), (∑ i : Fin 2, ‖φ i‖ * ‖φ i‖) = 1 →
      ∃ zs : List ℂ, zs.length = 4 ∧ (∀ z ∈ zs, ‖z‖ = 1) ∧
        clusterSequenceUnitary zs *ᵥ clusterPlusState = φ :=
  cluster_plus_word_surjectivity

theorem cluster_plus_full_scheme :
    ∀ φ : QState (Fin 2), (∑ i : Fin 2, ‖φ i‖ * ‖φ i‖) = 1 →
      ∃ zs : List ℂ, zs.length = 4 ∧ (∀ z ∈ zs, ‖z‖ = 1) ∧
        clusterSequenceUnitary zs *ᵥ clusterPlusState = φ ∧
        (∀ (ω v : Reg zs.length) (c : Fin 2),
          clusterPlusOutputVector zs ω
            (clusterSequenceRegisterEquiv zs.length (v, boolEquivFin2.symm c)) =
          if v = ω then ((Real.sqrt 2 : ℂ)⁻¹)^zs.length * φ c else 0) ∧
        (∀ ω : Reg zs.length,
          (observedLeaf 1 (clusterSequenceProgram zs) (clusterSequenceLeaf zs ω)).accepted = true ∧
          (observedLeaf 1 (clusterSequenceProgram zs) (clusterSequenceLeaf zs ω)).queries = 0 ∧
          (observedLeaf 1 (clusterSequenceProgram zs) (clusterSequenceLeaf zs ω)).measurements = zs.length ∧
          (observedLeaf 1 (clusterSequenceProgram zs) (clusterSequenceLeaf zs ω)).gates = 6 * zs.length - 1) :=
  cluster_plus_resource_preparation

theorem cluster_plus_output_density :
    ∀ φ : QState (Fin 2), (∑ i : Fin 2, ‖φ i‖ * ‖φ i‖) = 1 →
      ∃ zs : List ℂ, zs.length = 4 ∧ (∀ z ∈ zs, ‖z‖ = 1) ∧
        (∀ (ω : Reg zs.length) (c c' : Fin 2),
          (∑ v : Reg zs.length,
            clusterPlusOutputVector zs ω (clusterSequenceRegisterEquiv zs.length
              (v, boolEquivFin2.symm c)) *
            star (clusterPlusOutputVector zs ω (clusterSequenceRegisterEquiv zs.length
              (v, boolEquivFin2.symm c')))) =
            ((Real.sqrt 2 : ℂ)⁻¹)^(2 * zs.length) * φ c * star (φ c')) ∧
        (∀ ω : Reg zs.length, (∑ r : Fin (2 ^ (zs.length + 1)),
          ‖clusterPlusOutputVector zs ω r‖ * ‖clusterPlusOutputVector zs ω r‖) =
            (1 / 2 : ℝ)^zs.length) :=
  cluster_plus_resource_output_density

end Qatlib.Concepts.ClusterPatterns.Preentangled
