/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CryptoDisting99.Equivalence.Defs
import Qatlib.Papers.CryptoDisting99.Equivalence.Proposition1.Proposition1HelstromError
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CryptoDisting99.Equivalence

open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteInformationDivergence
open Qatlib.Concepts.MixedFidelity.FidelityMetric
open Matrix
open scoped BigOperators

theorem proposition3_kolmogorov_le_traceDistance {D : ℕ} (ρ σ : Operator D)
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    quantumKolmogorov ρ σ hρ hσ ≤ traceDistance ρ σ := by
  apply csSup_le
  · exact ⟨classicalKolmogorov
      (povmRecordLaw (trivialPOVM D) ρ hρ) (povmRecordLaw (trivialPOVM D) σ hσ),
      1, trivialPOVM D, rfl⟩
  · intro b hb
    obtain ⟨m, E, rfl⟩ := hb
    have h := Qatlib.Concepts.MixedFidelity.FidelityMetric.FinitePOVMTraceDistance.measured_tv_le
      E ρ σ hρ hσ
    unfold classicalKolmogorov traceDistance at *
    exact h

theorem proposition3_kolmogorov_eq_traceDistance {D : ℕ} (ρ σ : Operator D)
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    quantumKolmogorov ρ σ hρ hσ = traceDistance ρ σ := by
  apply le_antisymm (proposition3_kolmogorov_le_traceDistance ρ σ hρ hσ)
  obtain ⟨E, htv⟩ := helstrom_recordLaw_tv ρ σ hρ hσ
  unfold quantumKolmogorov
  rw [← htv]
  apply le_csSup
  · refine ⟨traceDistance ρ σ, ?_⟩
    rintro x ⟨m, E', rfl⟩
    have h := Qatlib.Concepts.MixedFidelity.FidelityMetric.FinitePOVMTraceDistance.measured_tv_le
      E' ρ σ hρ hσ
    unfold classicalKolmogorov traceDistance at *
    exact h
  · exact ⟨2, E, rfl⟩

end Qatlib.Papers.CryptoDisting99.Equivalence
