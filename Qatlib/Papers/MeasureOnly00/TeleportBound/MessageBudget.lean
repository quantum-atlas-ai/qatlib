/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MeasureOnly00.TeleportBound.MeasurementComposition

/-!
# Message tree budgets and resource ratios

`message_tree_budget` computes the depth, number of paths, and path encoding lengths of a
complete binary message tree. `resource_accounting_ratio` transports the macro gate to macro
measurement relation to the resource record of a run. The measurement-only computation context
is [RaussendorfBriegel2000].

## Main statements

* `message_tree_budget`: a depth `k` tree has `2 ^ k` paths encoded with length `k`.
* `resource_accounting_ratio`: macro gate count equals six times macro measurement count.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkDefs
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkLOCCDefs
open Qatlib.Papers.MeasureOnly00.TeleportBound

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MeasureOnly00.TeleportBound

open Matrix Qatlib

/-- The complete binary message tree of depth `k` has `2 ^ k` paths, each with an encoding of
length `k`. -/
theorem message_tree_budget (k : ℕ) :
    (completeTree k).depth = k ∧
    Fintype.card (completeTree k).Path = 2 ^ k ∧
    ∀ t : (completeTree k).Path, ((completeTree k).encode t).length = k :=
  clause4_message_budget k

/-- The resources extracted from a party plan run satisfy the equation that macro gate count is
six times macro measurement count. -/
theorem resource_accounting_ratio {D E : ℕ} {P : FiniteNetwork D E}
    (pl : PartyPlan P) (t : P.Transcript) (nativeGates : ℕ) :
    (resourceOfRun pl t nativeGates).ratio :=
  resourceOfRun_ratio pl t nativeGates

end Qatlib.Papers.MeasureOnly00.TeleportBound
