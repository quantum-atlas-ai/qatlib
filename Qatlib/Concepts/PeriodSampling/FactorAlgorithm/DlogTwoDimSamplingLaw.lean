/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.DlogSamplingLaw.DlogTwoDimSamplingLawAnsw

/-!
# Discrete-logarithm sampling-law interface

Re-exports the corrected two-dimensional discrete-logarithm sampling law in the factoring
namespace. The theorem `DlogTwoDimSamplingLaw_proof` supplies the normalized probability
formulas used by recovery consumers in the setting of [Shor1997].

## Main statements

* `DlogTwoDimSamplingLaw_proof`: Provides the corrected two-dimensional sampling-law contract.

## References

* [Shor, 1997][Shor1997]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PeriodSampling.DlogSamplingLaw

set_option autoImplicit false
namespace Qatlib.Concepts.PeriodSampling.FactorAlgorithm

/-- Re-exports the corrected two-dimensional discrete-logarithm sampling law associated with
[Shor1997]. -/
theorem DlogTwoDimSamplingLaw_proof : DlogTwoDimSamplingLaw := dlogTwoDimSamplingLaw
end Qatlib.Concepts.PeriodSampling.FactorAlgorithm
