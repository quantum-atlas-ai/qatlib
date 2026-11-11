/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.VaRQuantile.ReadoutMedianFiniteSubgoalStat
import Qatlib.Concepts.RiskEstimation.CDFEstimation.CDFActualFiniteSubgoalQuan
import Qatlib.Concepts.RiskEstimation.VaRQuantile.ReadoutMedianDefs

/-!
# Median cumulative-probability readout bound

`riskReadoutMedianFinite` proves the finite CDF readout specification by applying median
amplification to the amplitude-estimation mean law. It controls the probability that the
estimate differs from `riskCDF` by more than the uniform amplitude-estimation window, using the
method underlying [BrassardEtAl2002].

## Main statements

* `riskReadoutMedianFinite`: establish the CDF median failure bound `(8/9)^r`.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.RiskEstimation.CDFEstimation
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018

namespace Qatlib.Concepts.RiskEstimation.VaRQuantile
open Matrix
open scoped Classical BigOperators ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The median CDF estimator exceeds the error window `π/M + π²/M²` with probability at most
`(8/9)^r`. -/
theorem riskReadoutMedianFinite : ReadoutMedianFiniteSubgoal := by
  intro I _ _ A j loss t M r hA hM
  apply risk_median_tail
  · positivity
  · rw [riskCDF_eq]
    exact risk_mean_good A j (riskCDFPayoff loss t) M hA (riskCDFPayoff_bounds loss t) hM
end Qatlib.Concepts.RiskEstimation.VaRQuantile
