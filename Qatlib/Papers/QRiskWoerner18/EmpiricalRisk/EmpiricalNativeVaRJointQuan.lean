/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QRiskWoerner18.EmpiricalRisk.EmpiricalNativeVaRJointStat
import Qatlib.Concepts.RiskEstimation.VaRQuantile.NativeVaRFiniteRestrictedQuan

/-!
# Joint empirical value-at-risk guarantee

This module proves `empiricalNativeVaRJoint`, combining independent population samples and
native value-at-risk readout on a finite sorted loss grid. The result bounds failure of the
population CDF quantile brackets with an explicit sum of sampling and repeated-readout error
probabilities.

The source paper is [WoernerEgger2019].

## Main statements

* `empiricalNativeVaRJoint`: Establishes `EmpiricalNativeVaRJoint`, bounding the probability of
  an invalid returned index or violated population CDF quantile brackets under the stated
  sampling and precision conditions.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.FairRandomBits.EmpiricalWeight
open Qatlib.Concepts.NativeNumerics.EmpiricalRisk
open Qatlib.Concepts.SqEstimation.HierarchicalSQ
open Qatlib.Concepts.RiskEstimation.PopulationGap
open Qatlib.Concepts.RiskEstimation.VaRQuantile
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.LinearLearning.ConcisePipeline

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QRiskWoerner18.EmpiricalRisk
open scoped Classical BigOperators ENNReal
set_option warningAsError false

/-- Establishes `EmpiricalNativeVaRJoint`, bounding the probability of an invalid returned index
or violated population CDF quantile brackets under the stated sampling and precision
conditions [WoernerEgger2019]. -/
theorem empiricalNativeVaRJoint : EmpiricalNativeVaRJoint := by
  intro n N ebits bits M r p loss xs q ε ν hN hxs hsorted hsupport hq0 hq1 heps hν hM hwindow
  let B : (Fin N → Option (Fin n)) → Prop := fun ω =>
    ∃ t ∈ xs, ν < |(empiricalCDF ω loss t : ℝ)-populationCDF p loss t|
  let E : ℕ × ℕ → Prop := fun z =>
    z.1 ≥ xs.length ∨ populationCDF p loss (xs.getD z.1 0) < (q : ℝ)-((ε : ℝ)+ν+64*(n : ℝ)/2^ebits) ∨
      (z.1 ≠ 0 ∧ (q : ℝ)+((ε : ℝ)+ν+64*(n : ℝ)/2^ebits) < populationCDF p loss (xs.getD (z.1-1) 0))
  have hgood (ω : Fin N → Option (Fin n)) (hω : ¬ B ω) :
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (riskNativeVaR (empiricalPrepare ω ebits) none loss xs q bits M r (empiricalPrepare_unitary ω ebits) hM) E ≤
      ENNReal.ofReal ((Nat.clog 2 xs.length+1)*(8/9 : ℝ)^r) := by
    have hclose (i : ℕ) (hi : i < xs.length) :
        |riskCDF (empiricalPrepare ω ebits) none loss (xs.getD i 0) -
          populationCDF p loss (xs.getD i 0)| ≤ ν+64*(n : ℝ)/2^ebits := by
      have hm : xs.getD i 0 ∈ xs := by
        rw [List.getD_eq_getElem xs 0 hi]
        exact List.getElem_mem hi
      have hs : |(empiricalCDF ω loss (xs.getD i 0) : ℝ)-
          populationCDF p loss (xs.getD i 0)| ≤ ν := by
        by_contra h
        apply hω
        exact ⟨xs.getD i 0, hm, lt_of_not_ge h⟩
      have hb := (empirical_actual_preparation_cdf_bias n N ebits ω loss (xs.getD i 0) hN).2
      have ht := abs_sub_le (riskCDF (empiricalPrepare ω ebits) none loss (xs.getD i 0))
        (empiricalCDF ω loss (xs.getD i 0) : ℝ) (populationCDF p loss (xs.getD i 0))
      linarith
    apply (risk_event_mono _ (fun z hz => ?_)).trans
      (riskNativeVaRFinite (Option (Fin n)) (empiricalPrepare ω ebits) none loss xs q ε bits M r
        (empiricalPrepare_unitary ω ebits) hM hxs hsorted hsupport hq0 hq1 heps hwindow).1
    change E z at hz
    rcases hz with hlen | hlow | ⟨hne, hhigh⟩
    · exact Or.inl hlen
    · by_cases hi : z.1 < xs.length
      · right; left
        have hh := abs_le.mp (hclose z.1 hi)
        linarith
      · exact Or.inl (by omega)
    · by_cases hi : z.1 < xs.length
      · right; right
        refine ⟨hne, ?_⟩
        have hh := abs_le.mp (hclose (z.1-1) (by omega))
        linarith
      · exact Or.inl (by omega)
  have hb := risk_bind_failure
    (closurePMF (independentSampleLaw (fun _ : Fin N => p)))
    (fun ω => riskNativeVaR (empiricalPrepare ω ebits) none loss xs q bits M r (empiricalPrepare_unitary ω ebits) hM)
    B E (ENNReal.ofReal ((Nat.clog 2 xs.length+1)*(8/9 : ℝ)^r)) hgood
  apply hb.trans
  rw [risk_closure_event]
  have hs := empirical_uniform_cdf_sampling_bound n N p loss xs ν hN hν
  have hsn : 0 ≤ (xs.length : ℝ)/(4*(N : ℝ)*ν^2) := by positivity
  have han : 0 ≤ (Nat.clog 2 xs.length+1)*(8/9 : ℝ)^r := by positivity
  rw [ENNReal.ofReal_add hsn han]
  have hs' : Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass (independentSampleLaw (fun _ : Fin N => p)) B ≤
      (xs.length : ℝ)/(4*(N : ℝ)*ν^2) := by
    simpa only [Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass, B] using! hs
  exact add_le_add (ENNReal.ofReal_le_ofReal hs') le_rfl

end Qatlib.Papers.QRiskWoerner18.EmpiricalRisk
