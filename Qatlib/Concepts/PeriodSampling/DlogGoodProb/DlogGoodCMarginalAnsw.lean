/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.DlogGoodProb.DlogGoodCMarginalStat
import Qatlib.Concepts.PeriodSampling.DlogGoodProb.DlogOriginalContracts
import Qatlib.Concepts.PeriodSampling.DlogGoodProb.DlogGoodOutputProbabilityAnsw

/-!
# Discrete-logarithm marginal probability imports

Collects the marginal contract `DlogGoodCMarginal`, the legacy contracts, and the good-output
probability results needed for the marginal analysis. This import module introduces no
declarations of its own and belongs to the discrete-logarithm probability framework associated
with [Shor1997].

## Main statements

* `DlogGoodCMarginal`: The imported lower-bound contract for a small-residue first coordinate.
* `dlogGoodOutputProbability`: The imported good-output probability theorem.

## References

* [Shor, 1997][Shor1997]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.PeriodSampling.DlogGoodProb
open Qatlib
open scoped Classical BigOperators
set_option autoImplicit false

end Qatlib.Concepts.PeriodSampling.DlogGoodProb
