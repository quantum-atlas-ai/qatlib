/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.DlogCRTRecovery.DlogCandidateRecoveryAnsw

/-!
# Discrete-logarithm candidate recovery interface

Re-exports the candidate-recovery proof as `DlogCandidateRecovery_proof` in the factoring
namespace. This interface supplies the discrete-logarithm recovery contract used by the combined
algorithmic framework associated with [Shor1997].

## Main statements

* `DlogCandidateRecovery_proof`: Provides the imported candidate-recovery contract.

## References

* [Shor, 1997][Shor1997]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PeriodSampling.DlogCRTRecovery

set_option autoImplicit false
namespace Qatlib.Concepts.PeriodSampling.FactorAlgorithm

/-- Re-exports the discrete-logarithm candidate-recovery theorem from the recovery module
associated with [Shor1997]. -/
theorem DlogCandidateRecovery_proof : DlogCandidateRecovery := dlogCandidateRecovery
end Qatlib.Concepts.PeriodSampling.FactorAlgorithm
