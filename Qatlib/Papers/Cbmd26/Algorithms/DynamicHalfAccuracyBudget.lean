/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.DynamicFinalQueryBudget

/-!
# Dynamic query bounds at half accuracy

Controls the extra `dynamicDysonDegree` required when the simulation accuracy is halved. The
degree increases by at most a factor of three, which transfers the amplified dynamic query bound
to the fine-grid construction. These results support the contour-based algorithms of
[WangEtAl2026].

## Main statements

* `dynamicDysonDegree_half_le`: bounds the degree increase.
* `dynamicHalfAccuracy_amplified_query_bound`: gives the resulting amplified query bound.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SignalPrimitive.HermitianQSVT
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
noncomputable section
namespace CBMD

/-- Reducing a positive tolerance by a factor of four increases its dyadic order by at most two. -/
theorem dyadicOrder_quarter_le {δ : ℝ} (hδ : 0 < δ) :
    dyadicOrder (δ / 4) ≤ dyadicOrder δ + 2 := by
  have hd : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he : Real.log (δ / 4)⁻¹ / Real.log 2 = Real.log δ⁻¹ / Real.log 2 + 2 := by
    rw [show (δ/4)⁻¹ = 4 * δ⁻¹ by ring,
      Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (inv_ne_zero hδ.ne')]
    rw [show Real.log (4:ℝ) = 2 * Real.log 2 by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num]
    field_simp
    ring
  apply Nat.ceil_le.mpr
  rw [he, Nat.cast_add, Nat.cast_ofNat]
  have h := Nat.le_ceil (Real.log δ⁻¹ / Real.log 2)
  change Real.log δ⁻¹ / Real.log 2 ≤ (dyadicOrder δ : ℝ) at h
  linarith

/-- The chosen Dyson degree is positive for a positive segment count and accuracy in `(0, 1]`. -/
theorem dynamicDysonDegree_pos {S : ℕ} (hS : 0 < S) {ζ : ℝ}
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) : 0 < dynamicDysonDegree S ζ := by
  have hξ := dynamicSegmentAccuracy_bounds hS hζ hζ1
  have hp : 0 < dynamicSegmentAccuracy S ζ / 2 := by linarith
  have he := dyadicOrder_error hp
  change (1/2:ℝ)^dynamicDysonDegree S ζ ≤ _ at he
  by_contra hn
  have hn0 : dynamicDysonDegree S ζ = 0 := by omega
  rw [hn0, pow_zero] at he
  linarith [hξ.2]

/-- Halving a simulation accuracy in `(0, 1]` increases the chosen Dyson degree by at most a
factor of three. -/
theorem dynamicDysonDegree_half_le {S : ℕ} (hS : 0 < S) {ζ : ℝ}
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    dynamicDysonDegree S (ζ / 2) ≤ 3 * dynamicDysonDegree S ζ := by
  have hξ := (dynamicSegmentAccuracy_bounds hS hζ hζ1).1
  have he : dynamicSegmentAccuracy S (ζ/2) / 2 =
      (dynamicSegmentAccuracy S ζ / 2) / 4 := by unfold dynamicSegmentAccuracy; ring
  have hq := dyadicOrder_quarter_le (show 0 < dynamicSegmentAccuracy S ζ / 2 by positivity)
  have hn := dynamicDysonDegree_pos hS hζ hζ1
  unfold dynamicDysonDegree at *
  rw [he]
  omega

/-- The amplified segment-degree cost at half accuracy satisfies the displayed dynamic query
bound with an additional factor of three. -/
theorem dynamicHalfAccuracy_amplified_query_bound {α T ε η q : ℝ}
    (hα : 0 ≤ α) (hT : 0 ≤ T) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hη : 0 < η) (hη1 : η ≤ 1) (hq : 0 ≤ q) :
    let S := dynamicSegmentCount (staticKernelNormalization α (staticAnalyticBudget ε η)) T
    let ζ := dynamicSimulationAccuracy ε η
    ((4 * staticMassBudget + 1) / η) * q * ((S * dynamicDysonDegree S (ζ/2) : ℕ) : ℝ) ≤
      (3 * q * dynamicPaperQueryConstant) * ((1 + α * T) / η) *
        Real.log (2 / (ε * η)) * (Real.log (2 + α * T) + Real.log (2 / (ε * η))) := by
  (try dsimp only)
  have hΛ : 0 ≤ staticKernelNormalization α (staticAnalyticBudget ε η) := by
    unfold staticKernelNormalization
    exact mul_nonneg hα (by linarith [staticKernelFrequencyBound_pos (staticAnalyticBudget ε η)])
  have hS := (dynamicSegmentCount_bounds hΛ hT).1
  have hζ := dynamicSimulationAccuracy_bounds hε hε1 hη hη1
  have hk := Nat.mul_le_mul_left (dynamicSegmentCount
    (staticKernelNormalization α (staticAnalyticBudget ε η)) T)
      (dynamicDysonDegree_half_le hS hζ.1 hζ.2.1)
  have hkr : ((dynamicSegmentCount (staticKernelNormalization α (staticAnalyticBudget ε η)) T *
      dynamicDysonDegree (dynamicSegmentCount (staticKernelNormalization α (staticAnalyticBudget ε η)) T)
        (dynamicSimulationAccuracy ε η / 2) : ℕ) : ℝ) ≤
      3 * ((dynamicSegmentCount (staticKernelNormalization α (staticAnalyticBudget ε η)) T *
      dynamicDysonDegree (dynamicSegmentCount (staticKernelNormalization α (staticAnalyticBudget ε η)) T)
        (dynamicSimulationAccuracy ε η) : ℕ) : ℝ) := by
    exact_mod_cast (hk.trans_eq (by ring))
  have hc : 0 ≤ ((4 * staticMassBudget + 1) / η) * q := by
    have := staticMassBudget_ge_one
    positivity
  have hh := mul_le_mul_of_nonneg_left hkr hc
  have hb := dynamicChosen_amplified_query_bound hα hT hε hε1 hη hη1 (show 0 ≤ 3*q by positivity)
  (try dsimp only at hb)
  apply le_trans hh
  convert! hb using 1
  ring

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
