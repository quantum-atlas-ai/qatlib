/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpMmwSolver.SdpContract.RetainedContracts

/-!
# SDP rescaling contract

`SdpAlphaRescaleLemma2` names the retained coefficient-lifting and objective-rescaling
proposition. Its normalized tolerance is δ, giving the original objective upper bound (1 + δ)α.

For the mathematical background, see [BrandaoSvore2017].

## Main statements

* `SdpAlphaRescaleLemma2`: The retained lifting and rescaling contract extending `b` by the
  value R + 1 and converting a normalized bound of 1 + δ into an objective bound of (1 + δ)α.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.SdpMmwSolver.SdpContract

namespace Qatlib.Concepts.SdpMmwSolver.OracleError

/-- The retained lifting and rescaling contract extending `b` by the value R + 1 and converting
a normalized bound of 1 + δ into an objective bound of (1 + δ)α. -/
def SdpAlphaRescaleLemma2 : Prop := SdpAlphaRescaleLemma2Contract

end Qatlib.Concepts.SdpMmwSolver.OracleError
