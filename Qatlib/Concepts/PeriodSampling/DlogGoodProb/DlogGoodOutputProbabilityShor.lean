/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.DlogGoodProb.DlogGoodOutputProbabilityAnsw

/-!
# Good-output probability theorem interface

Re-exports `DlogGoodOutputProbability_proof` as the consumer-facing proof of the generator-based
good-output probability contract. The underlying estimates concern the two-dimensional
discrete-logarithm state associated with [Shor1997].

## Main statements

* `DlogGoodOutputProbability_proof`: Provides the good-output probability contract.

## References

* [Shor, 1997][Shor1997]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Concepts.PeriodSampling.DlogGoodProb

/-- Re-exports the proof of the generator-based good-output probability contract for the
discrete-logarithm state associated with [Shor1997]. -/
theorem DlogGoodOutputProbability_proof : DlogGoodOutputProbability := dlogGoodOutputProbability
end Qatlib.Concepts.PeriodSampling.DlogGoodProb
