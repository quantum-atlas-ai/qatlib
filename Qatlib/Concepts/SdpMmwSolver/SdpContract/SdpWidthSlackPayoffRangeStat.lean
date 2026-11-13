/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpMmwSolver.SdpContract.RetainedContracts

/-!
# Width-slack payoff range contract

`SdpWidthSlackPayoffRange` names the retained interval and cost guarantee with response width
α(1 + 2Rε). The hypotheses cap 2Rε by both 1/2 and δ/2.

For the mathematical background, see [BrandaoSvore2017].

## Main statements

* `SdpWidthSlackPayoffRange`: The retained contract guaranteeing Hermitian payoffs between zero
  and the identity and certificate cost at most (1 + δ)α when response width is α(1 + 2Rε).

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.SdpMmwSolver.SdpContract

/-- The retained contract guaranteeing Hermitian payoffs between zero and the identity and
certificate cost at most (1 + δ)α when response width is α(1 + 2Rε). -/
def SdpWidthSlackPayoffRange : Prop := SdpWidthSlackPayoffRangeContract

end Qatlib.Concepts.SdpMmwSolver.SdpContract
