/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QRiskWoerner18.EmpiricalRisk.EmpiricalNativeCVaRTargetErrorStat
import Qatlib.Concepts.RiskEstimation.CVaREstimation.NativeCVaRFiniteRestrictedQuan
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree

open Qatlib.Concepts.FairRandomBits.EmpiricalWeight
open Qatlib.Concepts.NativeNumerics.EmpiricalRisk
open Qatlib.Concepts.RiskEstimation.CVaREstimation
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QRiskWoerner18.EmpiricalRisk
open scoped Classical BigOperators ENNReal
set_option warningAsError false

theorem empiricalNativeCVaRTargetError : EmpiricalNativeCVaRTargetError := by
  intro n N ebits rotationBits bits M r ω loss t p μ η xs q ε v hN hloss hM hxs
    hsorted hsupport hq0 hq1 heps hv ht hwindow habove hbelow hden hη hc hm hp hgap
  have hbase := (riskNativeCVaRFinite (Option (Fin n)) (empiricalPrepare ω ebits)
    none loss xs q ε rotationBits bits M r v (empiricalPrepare_unitary ω ebits)
    hM hloss hxs hsorted hsupport hq0 hq1 heps hv hwindow
    (by simpa only [ht] using! habove) hbelow (by simpa only [ht] using! hden)).1
  have htail := empirical_tail_ratio_stability n N ebits ω loss t p μ η hN hloss hη hc hm hp hgap
  apply (risk_event_mono _ (fun z hz => ?_)).trans hbase
  rcases hz with hbad | herr
  · exact Or.inl hbad
  · right
    rw [ht]
    have htri := abs_sub_le (z.2.1 : ℝ) (riskTailMean (empiricalPrepare ω ebits) none loss t) (μ/p)
    linarith

end Qatlib.Papers.QRiskWoerner18.EmpiricalRisk
