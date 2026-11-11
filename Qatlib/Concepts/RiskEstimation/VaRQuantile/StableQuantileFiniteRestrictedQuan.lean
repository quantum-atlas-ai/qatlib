/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.VaRQuantile.StableQuantileFiniteRestrictedStat
import Qatlib.Concepts.RiskEstimation.VaRQuantile.VaRAlgorithmFiniteRestrictedQuan
import Qatlib.Concepts.RiskEstimation.VaRQuantile.StableQuantileDefs

/-!
# Recovery of a separated finite quantile

`riskStableQuantileFinite` proves that `riskVaR` returns a specified quantile index with high
probability when the CDF values have the required margin around the target. It combines the
approximate-bracket estimate with `risk_stable_wrong_index`, yielding a depth-weighted median
failure bound for the search of [WoernerEgger2019].

## Main statements

* `riskStableQuantileFinite`: establish the finite separated-quantile recovery contract.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018

namespace Qatlib.Concepts.RiskEstimation.VaRQuantile
open Matrix
open scoped Classical BigOperators ENNReal
set_option autoImplicit false

/-- Under the separated-quantile and readout-window assumptions, `riskVaR` returns an index
unequal to `v` with probability at most `(Nat.clog 2 xs.length + 1) * (8/9)^r`. This is the
stable quantile case of the search in [Woerner and Egger, Section II][WoernerEgger2019]. -/
theorem riskStableQuantileFinite : StableQuantileFiniteRestricted := by
  intro I _ _ A j loss xs q eps M r v hA hM hxs hs hloss hq0 hq1 heps hv hwindow habove hbelow
  apply le_trans
      (risk_event_mono _ (risk_stable_wrong_index A j loss xs q eps v hs hv habove hbelow))
  exact riskVaRAlgorithmFinite I A j loss xs q eps M r hA hM hxs hs hloss hq0 hq1 heps hwindow
end Qatlib.Concepts.RiskEstimation.VaRQuantile
