/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.VaRQuantile.StableQuantileFiniteRestrictedStat
import Qatlib.Concepts.RiskEstimation.VaRQuantile.VaRAlgorithmFiniteRestrictedQuan
import Qatlib.Concepts.RiskEstimation.VaRQuantile.StableQuantileDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018

namespace Qatlib.Concepts.RiskEstimation.VaRQuantile
open Matrix
open scoped Classical BigOperators ENNReal
set_option autoImplicit false

theorem riskStableQuantileFinite : StableQuantileFiniteRestricted := by
  intro I _ _ A j loss xs q eps M r v hA hM hxs hs hloss hq0 hq1 heps hv hwindow habove hbelow
  apply le_trans
      (risk_event_mono _ (risk_stable_wrong_index A j loss xs q eps v hs hv habove hbelow))
  exact riskVaRAlgorithmFinite I A j loss xs q eps M r hA hM hxs hs hloss hq0 hq1 heps hwindow
end Qatlib.Concepts.RiskEstimation.VaRQuantile
