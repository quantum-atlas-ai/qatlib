/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkLOCC
import Qatlib.Concepts.MbqcFlow.FlowDecision.PureToMixedConditional

/-!
# Resource counts and message budget definitions

`Clause6Resource` records macro gates, macro measurements, and classical bits, with
`Clause6Resource.ratio` stating the prescribed gate to measurement relation.
`Clause7MessageBudget` records tree depth, path count, and encoding length; `Clause7GuessBound`
defines the real ratio of message count to input count. The measurement-only computation context
is [RaussendorfBriegel2000].

## Main statements

* `Clause6Resource.ratio`: the equation relating macro gate and measurement counts.
* `Clause7GuessBound`: message count multiplied by reciprocal input count.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Papers.MeasureOnly00.TeleportBound

/-- A record of macro gate count, macro measurement count, and classical bit count. -/
structure Clause6Resource where

  macroGates : ℕ

  macroMeasurements : ℕ

  classicalBits : ℕ

/-- The condition that the macro gate count equals six times the macro measurement count. -/
def Clause6Resource.ratio (r : Clause6Resource) : Prop := r.macroGates = 6 * r.macroMeasurements

/-- A record of message tree depth, number of paths, and encoding length. -/
structure Clause7MessageBudget where

  depth : ℕ

  paths : ℕ

  encodeLength : ℕ

/-- The real-valued expression `messages * (1 / inputs)` for natural message and input counts. -/
noncomputable def Clause7GuessBound (messages inputs : ℕ) : ℝ :=
  (messages : ℝ) * (1 / (inputs : ℝ))

end Qatlib.Papers.MeasureOnly00.TeleportBound
