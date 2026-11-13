/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpMmwSolver.MmwCore.SdpLemma7SourceCoefficientsStat
import Qatlib.Concepts.MatrixWeights.LambdaMin

/-!
# Source coefficients for the matrix weights bound

`sdpLemma7SourceCoefficients` establishes the matrix multiplicative weights estimate with
learning rate −log(1 − ε). It selects a minimum eigenvalue of the cumulative payoff and bounds
the actual cumulative Gibbs payoff using coefficient 1 + ε and additive term log(D)/ε.

For the mathematical background, see [BrandaoSvore2017].

## Main statements

* `sdpLemma7SourceCoefficients`: For positive semidefinite payoffs bounded by the identity and 0
  < ε < 1/2, the cumulative Gibbs payoff at rate −log(1 − ε) is bounded by (1 + ε) times a
  minimum cumulative eigenvalue plus log(D)/ε. See [BrandaoSvore2017].

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.MatrixWeights.LambdaMin

namespace Qatlib.Concepts.SdpMmwSolver.MmwCore

/-- For positive semidefinite payoffs bounded by the identity and 0 < ε < 1/2, the cumulative
Gibbs payoff at rate −log(1 − ε) is bounded by (1 + ε) times a minimum cumulative eigenvalue
plus log(D)/ε. See [BrandaoSvore2017]. -/
theorem sdpLemma7SourceCoefficients : SdpLemma7SourceCoefficients := by
  exact matrix_mw_source_min_eigenvalue

end Qatlib.Concepts.SdpMmwSolver.MmwCore
