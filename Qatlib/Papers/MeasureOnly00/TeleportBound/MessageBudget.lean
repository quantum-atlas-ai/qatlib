/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MeasureOnly00.TeleportBound.MeasurementComposition
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkDefs
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkLOCCDefs
open Qatlib.Papers.MeasureOnly00.TeleportBound

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MeasureOnly00.TeleportBound

open Matrix Qatlib

theorem message_tree_budget (k : ℕ) :
    (completeTree k).depth = k ∧
    Fintype.card (completeTree k).Path = 2 ^ k ∧
    ∀ t : (completeTree k).Path, ((completeTree k).encode t).length = k :=
  clause4_message_budget k

theorem resource_accounting_ratio {D E : ℕ} {P : FiniteNetwork D E}
    (pl : PartyPlan P) (t : P.Transcript) (nativeGates : ℕ) :
    (resourceOfRun pl t nativeGates).ratio :=
  resourceOfRun_ratio pl t nativeGates

end Qatlib.Papers.MeasureOnly00.TeleportBound
