/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.AmplitudeCore.InvFreeSampling.InvFreeAESemantics
public import Qatlib.Concepts.AmplitudeCore.InvFreeSampling.InverseFreeAESamplingBoundStat
public import Qatlib.Concepts.AmplitudeCore.InvFreeSampling.BernoulliTail

@[expose] public section
open Qatlib.Concepts.AmplitudeCore.InvFreeSampling Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.PureStateMath Qatlib.Foundations.QueryWordCore.Circuit

namespace Qatlib.Concepts.AmplitudeCore.InvFreeSampling

open Qatlib

/-- Establishes the inverse-free amplitude estimation sampling bound specified by
`InverseFreeAESamplingBound`. -/
theorem inverseFreeAESamplingBound : InverseFreeAESamplingBound := by
  intro I _ _ P hP j₀ ε hε0 hε1 U hU
  have hε2 : (0:ℝ) < ε ^ 2 := by nlinarith
  have hpos : (0:ℝ) < 3 / (4 * ε ^ 2) :=
    div_pos (by norm_num) (by nlinarith : (0:ℝ) < 4 * ε ^ 2)
  have hLnat : 0 < invFreeSampleCount ε := by
    simp only [invFreeSampleCount]
    exact Nat.ceil_pos.mpr hpos
  set p := invFreeBranchDist P j₀ hP U hU with hp
  have hap : p.expect boolIndicator = invFreeAmplitude P j₀ U := by
    rw [← invFree_expect_amplitude P j₀ hP U hU]
    rfl
  have hcheb := chebyshev_avg_boolIndicator p hLnat ε hε0
  have hLge : 3 / (4 * ε ^ 2) ≤ (invFreeSampleCount ε : ℝ) := by
    have hceil := Nat.le_ceil (3 / (4 * ε ^ 2))
    simp only [invFreeSampleCount]
    exact_mod_cast hceil
  have h34 : (1:ℝ) / (4 * (invFreeSampleCount ε : ℝ) * ε ^ 2) ≤ 1 / 3 := by
    have h4 : (3:ℝ) ≤ 4 * (invFreeSampleCount ε : ℝ) * ε ^ 2 := by
      have h := hLge
      rw [div_le_iff₀ (by nlinarith : (0:ℝ) < 4 * ε ^ 2)] at h
      have hring : 4 * (invFreeSampleCount ε : ℝ) * ε ^ 2
          = (invFreeSampleCount ε : ℝ) * (4 * ε ^ 2) := by ring
      rw [hring]
      exact h
    rw [one_div_le_one_div (by nlinarith) (by norm_num)]
    linarith
  have hgood : 2 / 3 ≤ p.probEvent
      (fun ω : Fin (invFreeSampleCount ε) → Bool =>
        |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg invFreeReadout ω - invFreeAmplitude P j₀ U| ≤ ε) := by
    have hcompl := probEvent_compl p
      (fun ω : Fin (invFreeSampleCount ε) → Bool =>
        |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg invFreeReadout ω - invFreeAmplitude P j₀ U| ≤ ε)
    have hcongr : p.probEvent
        (fun ω : Fin (invFreeSampleCount ε) → Bool =>
          ¬(|Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg invFreeReadout ω - invFreeAmplitude P j₀ U| ≤ ε))
        = p.probEvent
          (fun ω : Fin (invFreeSampleCount ε) → Bool =>
            ε < |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg boolIndicator ω - p.expect boolIndicator|) :=
      probEvent_congr p _ _ (fun ω => by
        rw [hap]
        exact not_le)
    have hsplit : p.probEvent
        (fun ω : Fin (invFreeSampleCount ε) → Bool =>
          |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg invFreeReadout ω - invFreeAmplitude P j₀ U| ≤ ε)
        = 1 - p.probEvent
          (fun ω : Fin (invFreeSampleCount ε) → Bool =>
            ε < |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg boolIndicator ω - p.expect boolIndicator|) := by
      rw [← hcongr]
      linarith
    rw [hsplit]
    have hcast : (invFreeSampleCount ε : ℝ) = ((invFreeSampleCount ε : ℕ) : ℝ) := rfl
    linarith [hcheb, h34]
  exact hgood

/-- Bounds the inverse-free sample count by seven divided by four times the squared error
tolerance. -/
theorem inverseFreeAESamplingBound_query_count (ε : ℝ) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) :
    (invFreeSampleCount ε : ℝ) ≤ 7 / (4 * ε ^ 2) := by
  have hε2 : (0:ℝ) < ε ^ 2 := by nlinarith
  have hε2le1 : ε ^ 2 ≤ 1 := by nlinarith
  have hpos : (0:ℝ) < 3 / (4 * ε ^ 2) :=
    div_pos (by norm_num) (by nlinarith : (0:ℝ) < 4 * ε ^ 2)
  have hlt : (invFreeSampleCount ε : ℝ) < 3 / (4 * ε ^ 2) + 1 := by
    have hceil := Nat.ceil_lt_add_one (le_of_lt hpos)
    simpa only [invFreeSampleCount] using hceil
  have h1 : (3:ℝ) / (4 * ε ^ 2) + 1 ≤ 7 / (4 * ε ^ 2) := by
    apply sub_nonneg.mp
    have hdiff : (7:ℝ) / (4 * ε ^ 2) - (3 / (4 * ε ^ 2) + 1) = (1 - ε ^ 2) / ε ^ 2 := by
      field_simp
      ring
    rw [hdiff]
    apply div_nonneg <;> nlinarith
  linarith

end Qatlib.Concepts.AmplitudeCore.InvFreeSampling
