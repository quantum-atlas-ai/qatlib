/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkLOCC
import Qatlib.Concepts.MbqcFlow.FlowDecision.PureToMixedConditional
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Papers.MeasureOnly00.TeleportBound

structure Clause6Resource where

  macroGates : ℕ

  macroMeasurements : ℕ

  classicalBits : ℕ

def Clause6Resource.ratio (r : Clause6Resource) : Prop := r.macroGates = 6 * r.macroMeasurements

structure Clause7MessageBudget where

  depth : ℕ

  paths : ℕ

  encodeLength : ℕ

noncomputable def Clause7GuessBound (messages inputs : ℕ) : ℝ :=
  (messages : ℝ) * (1 / (inputs : ℝ))

end Qatlib.Papers.MeasureOnly00.TeleportBound
