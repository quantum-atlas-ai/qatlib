/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MeasureOnly00.TeleportBound.MeasurementCompositionDefs
import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkLOCC
import Qatlib.Concepts.MbqcFlow.FlowDecision.PureToMixedConditional
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkDefs
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkLOCCDefs

namespace Qatlib.Papers.MeasureOnly00.TeleportBound

open Matrix

theorem clause3_mixed_pure_equivalence {D : ℕ} {ρ : Operator D} (hρ : IsDensityOperator ρ) :
    ∃ (w : Fin D → ℝ) (ψ : Fin D → QState (Fin D)),
      (∀ k, 0 ≤ w k) ∧ (∀ k, Normalized (ψ k)) ∧ (∑ k, w k = 1) ∧
        ρ = ∑ k, (w k : ℂ) • outerProduct (ψ k) :=
  density_pure_decomposition ρ hρ

noncomputable def resourceOfRun {D E : ℕ} {P : FiniteNetwork D E}
    (pl : PartyPlan P) (t : P.Transcript) (nativeGates : ℕ) : Clause6Resource where
  macroGates := (pl.cost t nativeGates).macroGates
  macroMeasurements := (pl.cost t nativeGates).macroMeasurements
  classicalBits := (pl.cost t nativeGates).classicalBits

theorem resourceOfRun_ratio {D E : ℕ} {P : FiniteNetwork D E}
    (pl : PartyPlan P) (t : P.Transcript) (nativeGates : ℕ) :
    (resourceOfRun pl t nativeGates).ratio :=
  cost_macro_gates pl t nativeGates

theorem clause4_message_budget (k : ℕ) :
    (completeTree k).depth = k ∧
    Fintype.card (completeTree k).Path = 2 ^ k ∧
    ∀ t : (completeTree k).Path, ((completeTree k).encode t).length = k :=
  ⟨completeTree_depth k, completeTree_card k, completeTree_encode_length k⟩

end Qatlib.Papers.MeasureOnly00.TeleportBound
