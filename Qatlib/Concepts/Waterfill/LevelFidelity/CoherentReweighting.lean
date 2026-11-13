/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WaterLevel.WaterPrecision.CoherentReweightingDefs

/-!
# Shared definitions for coherent reweighting

This module imports the common coherent-reweighting definitions, including `realFill`,
`realFidelity`, `fidelityBracket`, and `ReweightingSuccess`. It provides the namespace and
shared context used by subsequent real-table and rational-search developments.

The underlying water-level framework is motivated by quantum rejection sampling
[OzolsRoettelerRoland2013], studied by [Ozols et al., 2013][OzolsRoettelerRoland2013].
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.Waterfill.LevelFidelity

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Matrix
open Qatlib
open Qatlib.Concepts.Waterfill.ExactResampling
open Qatlib
open Qatlib.Concepts.Waterfill.LevelFidelity.WaterLevelFidelity
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.WaterLevel.WaterPrecision
open scoped BigOperators ComplexOrder

section RealChain

variable {m : ℕ} (π σ : Fin m → ℝ)

end RealChain

section SearchHelpers

variable {m : ℕ} (π σ : Fin m → ℚ)

end SearchHelpers

end Qatlib.Concepts.Waterfill.LevelFidelity
