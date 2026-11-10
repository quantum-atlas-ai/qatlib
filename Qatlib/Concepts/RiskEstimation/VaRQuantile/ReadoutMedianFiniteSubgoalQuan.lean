/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.VaRQuantile.ReadoutMedianFiniteSubgoalStat
import Qatlib.Concepts.RiskEstimation.CDFEstimation.CDFActualFiniteSubgoalQuan
import Qatlib.Concepts.RiskEstimation.VaRQuantile.ReadoutMedianDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.RiskEstimation.CDFEstimation
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018

namespace Qatlib.Concepts.RiskEstimation.VaRQuantile
open Matrix
open scoped Classical BigOperators ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem riskReadoutMedianFinite : ReadoutMedianFiniteSubgoal := by
  intro I _ _ A j loss t M r hA hM
  apply risk_median_tail
  · positivity
  · rw [riskCDF_eq]
    exact risk_mean_good A j (riskCDFPayoff loss t) M hA (riskCDFPayoff_bounds loss t) hM
end Qatlib.Concepts.RiskEstimation.VaRQuantile
