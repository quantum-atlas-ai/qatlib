/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsDefs
import Qatlib.Concepts.AdaptiveCP.BranchTrace.StoppingJointDefs
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution

namespace Qatlib.Concepts.ShadowModels.FairBitRecords

open Matrix
open Qatlib
open scoped BigOperators Classical ComplexOrder ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable def fairBitMass (k : ℕ) : ℝ≥0∞ := ((2 ^ k : ℕ) : ℝ≥0∞)⁻¹

noncomputable def fairBitMassReal (k : ℕ) : ℝ := ENNReal.toReal (fairBitMass k)

noncomputable def fairBitRejectedMass (k m : ℕ) : ℝ≥0∞ := coinRejectMass k m

end Qatlib.Concepts.ShadowModels.FairBitRecords
