/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpMmwSolver.SdpContract.RetainedContracts

/-!
# Source-coefficient matrix weights contract

`SdpLemma7SourceCoefficients` names the retained matrix multiplicative weights contract. It
compares cumulative Gibbs payoff with a minimum eigenvalue of the cumulative payoff matrix at
learning rate −log(1 − ε).

For the mathematical background, see [BrandaoSvore2017].

## Main statements

* `SdpLemma7SourceCoefficients`: The retained contract bounding cumulative Gibbs payoff by (1 +
  ε) times a minimum cumulative eigenvalue plus log(D)/ε for 0 < ε < 1/2.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.SdpMmwSolver.SdpContract

namespace Qatlib.Concepts.SdpMmwSolver.MmwCore

/-- The retained contract bounding cumulative Gibbs payoff by (1 + ε) times a minimum cumulative
eigenvalue plus log(D)/ε for 0 < ε < 1/2. -/
def SdpLemma7SourceCoefficients : Prop := SdpLemma7SourceCoefficientsContract

end Qatlib.Concepts.SdpMmwSolver.MmwCore
