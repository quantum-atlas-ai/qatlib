/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MeasureOnly00.TeleportBound.MeasurementCompositionDefs
import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkLOCC
import Qatlib.Concepts.MbqcFlow.FlowDecision.PureToMixedConditional

/-!
# Composition and measurement resource accounting

`clause3_mixed_pure_equivalence` expresses a density operator as a convex combination of
normalized pure states. `resourceOfRun` extracts macro gate, macro measurement, and classical
bit counts from a party plan transcript, and the module proves their prescribed ratio and the
complete binary message tree budget. The measurement-only computation context is
[RaussendorfBriegel2000].

## Main statements

* `resourceOfRun_ratio`: macro gate count is six times macro measurement count.
* `clause4_message_budget`: depth, path count, and encoding length of a complete message tree.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkDefs
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkLOCCDefs

namespace Qatlib.Papers.MeasureOnly00.TeleportBound

open Matrix

/-- Every density operator is a convex combination of `D` normalized pure state outer products,
with nonnegative real weights summing to one. -/
theorem clause3_mixed_pure_equivalence {D : ℕ} {ρ : Operator D} (hρ : IsDensityOperator ρ) :
    ∃ (w : Fin D → ℝ) (ψ : Fin D → QState (Fin D)),
      (∀ k, 0 ≤ w k) ∧ (∀ k, Normalized (ψ k)) ∧ (∑ k, w k = 1) ∧
        ρ = ∑ k, (w k : ℂ) • outerProduct (ψ k) :=
  density_pure_decomposition ρ hρ

/-- The resource record obtained from a party plan's cost on a transcript and a supplied native
gate count. -/
noncomputable def resourceOfRun {D E : ℕ} {P : FiniteNetwork D E}
    (pl : PartyPlan P) (t : P.Transcript) (nativeGates : ℕ) : Clause6Resource where
  macroGates := (pl.cost t nativeGates).macroGates
  macroMeasurements := (pl.cost t nativeGates).macroMeasurements
  classicalBits := (pl.cost t nativeGates).classicalBits

/-- The resource record of a run has macro gate count equal to six times its macro measurement
count. -/
theorem resourceOfRun_ratio {D E : ℕ} {P : FiniteNetwork D E}
    (pl : PartyPlan P) (t : P.Transcript) (nativeGates : ℕ) :
    (resourceOfRun pl t nativeGates).ratio :=
  cost_macro_gates pl t nativeGates

/-- The complete binary message tree of depth `k` has `2 ^ k` paths, and every encoded path has
length `k`. -/
theorem clause4_message_budget (k : ℕ) :
    (completeTree k).depth = k ∧
    Fintype.card (completeTree k).Path = 2 ^ k ∧
    ∀ t : (completeTree k).Path, ((completeTree k).encode t).length = k :=
  ⟨completeTree_depth k, completeTree_card k, completeTree_encode_length k⟩

end Qatlib.Papers.MeasureOnly00.TeleportBound
