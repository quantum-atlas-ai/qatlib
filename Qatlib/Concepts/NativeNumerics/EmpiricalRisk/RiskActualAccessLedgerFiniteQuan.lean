/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.NativeNumerics.EmpiricalRisk.RiskActualAccessLedgerFiniteStat
import Qatlib.Concepts.RiskEstimation.CVaREstimation.CVaRAlgorithmFiniteRestrictedQuan
import Qatlib.Concepts.NativeNumerics.EmpiricalRisk.RiskAccessLedgerDefs

/-!
# Finite quantum risk access ledger

This module proves `RiskActualAccessLedgerFiniteSubgoal` by combining the support bound for
`riskCVaR` with the separate preparation-access counts and the query and gate counts of counted
amplitude estimation. It provides a resource ledger for the risk-estimation setting of
[WoernerEgger2019] and the amplitude-estimation framework of [BrassardEtAl2002].

## Main statements

* `riskActualAccessLedgerFinite`: the CVaR call budget is exceeded with probability zero, and
  the amplitude-estimation access, query, and gate counts have the prescribed exact values.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.RiskEstimation.VaRQuantile
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018

namespace Qatlib.Concepts.NativeNumerics.EmpiricalRisk
open Matrix
open scoped Classical BigOperators ENNReal
set_option autoImplicit false

/-- Establish `RiskActualAccessLedgerFiniteSubgoal`, including the almost-sure CVaR call bound
and exact amplitude-estimation preparation-access, query, and gate counts. -/
theorem riskActualAccessLedgerFinite : RiskActualAccessLedgerFiniteSubgoal := by
  intro I _ _ A j loss xs q eps k M r hA hloss hM _hxs
  have hpos : 0 < M := by omega
  have hsep := prepared_ae_separate_access_counts (I := I × Bool) M hpos
  have hcount :=
      prepared_ae_access_ledger M hpos (payoffPreparation A (riskCDFPayoff loss 0)) (j,false)
  refine ⟨?_, hsep.1, hsep.2.1, hcount.1, hcount.2.1⟩
  apply risk_event_zero_support
  intro z hz
  exact not_lt_of_ge (riskCVaR_support_calls A j loss xs q eps k M r hA hloss hM z hz)
end Qatlib.Concepts.NativeNumerics.EmpiricalRisk
