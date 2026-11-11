/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpMmwSolver.SdpContract.RetainedContracts

/-!
# Convex sampling contract

`SdpConvexCombinationSampling` names the retained contract for sampling a dual certificate. The
proposition specifies a positive scale, a normalized nonnegative distribution, and explicit
weights for the correction term and the T round contributions.

For the mathematical background, see [BrandaoSvore2017].

## Main statements

* `SdpConvexCombinationSampling`: The retained contract for representing the dual certificate by
  a positive scale, a probability distribution, and convex weights for its correction and round
  terms.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.SdpMmwSolver.SdpContract

/-- The retained contract for representing the dual certificate by a positive scale, a
probability distribution, and convex weights for its correction and round terms. -/
def SdpConvexCombinationSampling : Prop := SdpConvexCombinationSamplingContract

end Qatlib.Concepts.SdpMmwSolver.SdpContract
