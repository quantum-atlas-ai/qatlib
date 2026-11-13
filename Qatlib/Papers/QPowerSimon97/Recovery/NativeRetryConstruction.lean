/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPowerSimon97.Recovery.NativeRetryConstructionDefs
import Qatlib.Concepts.HspRecovery.Distinguisher.BoundedErrorNearPeriodSimo

/-!
# Native Simon retry construction interface

Imports the native retry definitions and the near-period distinguisher results used in the
construction associated with [Simon1997]. The imported `SimonQueryTree`, `simonFreshRuns`, and
`simonAmplifiedReject` provide the classical query and repeated-experiment interfaces; this file
introduces no additional mathematical declarations.

## Main definitions

* `SimonQueryTree`: finite adaptive classical query trees with Boolean outputs.
* `simonFreshRuns`: independent decoded Simon runs.
* `simonAmplifiedReject`: the Boolean law reporting whether any run differs from the decoded
  zero result.

## References

* [Simon, 1997][Simon1997]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.HspRecovery.Distinguisher

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QPowerSimon97.Recovery
open Qatlib.Concepts.AbelianDecoders.SimonDecoding Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian Qatlib.Concepts.HspRecovery.Distinguisher
open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Concepts.QtmSimulation.Phi3Compilation
open Qatlib.Concepts.UniformBqp.Phi3Compile
open Qatlib.Concepts.CircuitImpl.Phi3Universal
open Matrix
open scoped Classical BigOperators ENNReal

namespace SimonQueryTree

variable {n : ℕ}

end SimonQueryTree

namespace SimonQueryTree

variable {n : ℕ}

end SimonQueryTree

namespace SimonQueryTree

variable {n : ℕ}

end SimonQueryTree

namespace SimonQueryTree

variable {n : ℕ}

end SimonQueryTree

namespace SimonAssembly

end SimonAssembly

end Qatlib.Papers.QPowerSimon97.Recovery
