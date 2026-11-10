/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CryptoDisting99.Equivalence.Defs
import Qatlib.Papers.CryptoDisting99.Equivalence.Proposition2
import Qatlib.Papers.CryptoDisting99.Equivalence.Proposition1.HelstromAchievability
import Qatlib.Concepts.MixedFidelity.FidelityMetric.ChannelHelpers.FinitePOVMTraceDistance
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

def trivialPOVM (D : ℕ) : FinitePOVM (Fin 1) D where
  effect := fun _ => 1
  effect_sum := by simp
  weight := fun _ => 1
  weight_nonneg := fun _ => zero_le_one
  factor := fun _ => 1
  effect_eq_factor := by intro o; simp

lemma classicalErrProb_povmRecordLaw_ge {D m : ℕ} (E : FinitePOVM (Fin m) D)
    (ρ σ : Operator D) (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    1 / 2 - traceDistance ρ σ / 2 ≤
      classicalErrProb (povmRecordLaw E ρ hρ) (povmRecordLaw E σ hσ) := by
  rw [proposition2_error_eq_kolmogorov]
  have h := Qatlib.Concepts.MixedFidelity.FidelityMetric.FinitePOVMTraceDistance.measured_tv_le
    E ρ σ hρ hσ
  unfold classicalKolmogorov traceDistance at *
  linarith

theorem proposition1_error_lower_bound {D : ℕ} (ρ σ : Operator D)
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    1 / 2 - traceDistance ρ σ / 2 ≤ quantumErrProb ρ σ hρ hσ := by
  apply le_csInf
  · exact ⟨classicalErrProb
      (povmRecordLaw (trivialPOVM D) ρ hρ) (povmRecordLaw (trivialPOVM D) σ hσ),
      1, trivialPOVM D, rfl⟩
  · intro b hb
    obtain ⟨m, E, rfl⟩ := hb
    exact classicalErrProb_povmRecordLaw_ge E ρ σ hρ hσ

theorem proposition1_error_eq {D : ℕ} (ρ σ : Operator D)
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    quantumErrProb ρ σ hρ hσ = 1 / 2 - traceDistance ρ σ / 2 := by
  apply le_antisymm
  · unfold quantumErrProb
    obtain ⟨E, htv⟩ := helstrom_recordLaw_tv ρ σ hρ hσ
    have hbdd : BddBelow { x : ℝ | ∃ (m : ℕ) (E : FinitePOVM (Fin m) D),
        x = classicalErrProb (povmRecordLaw E ρ hρ) (povmRecordLaw E σ hσ) } := by
      refine ⟨0, ?_⟩
      rintro x ⟨m, E', rfl⟩
      unfold classicalErrProb
      apply mul_nonneg (by norm_num)
      exact Finset.sum_nonneg fun i _ =>
        le_min ((povmRecordLaw E' ρ hρ).nonneg i) ((povmRecordLaw E' σ hσ).nonneg i)
    have hle := csInf_le hbdd (show
      classicalErrProb (povmRecordLaw E ρ hρ) (povmRecordLaw E σ hσ) ∈
        { x : ℝ | ∃ (m : ℕ) (E : FinitePOVM (Fin m) D),
          x = classicalErrProb (povmRecordLaw E ρ hρ) (povmRecordLaw E σ hσ) } from ⟨2, E, rfl⟩)
    have hval : classicalErrProb (povmRecordLaw E ρ hρ) (povmRecordLaw E σ hσ) =
        1 / 2 - traceDistance ρ σ / 2 := by
      rw [proposition2_error_eq_kolmogorov, htv]
    rwa [hval] at hle
  · exact proposition1_error_lower_bound ρ σ hρ hσ

end Qatlib.Papers.CryptoDisting99.Equivalence
