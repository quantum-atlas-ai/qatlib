/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.DynamicCBMDParameters
import Qatlib.Papers.Cbmd26.Algorithms.OutputNormEstimateBudget

/-!
# Final logarithmic dynamic query bounds

Combines the chosen segment and Dyson-degree bounds into an explicit product estimate using
`dynamicDegreeConstant`. The bound `dynamicChosen_amplified_query_bound` includes amplification,
while `dynamic_true_output_query_bound` compares estimated and true output norms. These results
support the contour-based algorithms of [WangEtAl2026].

## Main statements

* `dynamicChosen_amplified_query_bound`: bounds amplified segment-degree costs.
* `dynamic_true_output_query_bound`: replaces an output estimate by a comparable true norm.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
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
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
noncomputable section
namespace CBMD

/-- Defines the positive logarithmic constant used to bound the chosen dynamic degree. -/
def dynamicDegreeConstant : ℝ :=
  (Real.log 20 + 2 * Real.log 15 + 6) / Real.log 2 + 1

/-- The dynamic degree constant is positive. -/
theorem dynamicDegreeConstant_pos : 0 < dynamicDegreeConstant := by
  have hd : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h20 : 0 < Real.log 20 := Real.log_pos (by norm_num)
  have h15 : 0 < Real.log 15 := Real.log_pos (by norm_num)
  unfold dynamicDegreeConstant
  positivity

/-- The logarithm of the reciprocal simulation accuracy is bounded by `log
(staticQueryLogConstant / (ε * η))`. -/
theorem dynamic_inverse_precision_log_le {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) :
    Real.log (dynamicSimulationAccuracy ε η)⁻¹ ≤
      Real.log (staticQueryLogConstant / (ε * η)) := by
  have hC := staticMassBudget_ge_one
  have hT := _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.kernelTailConstant_pos
  have hE := Real.exp_pos (1:ℝ)
  have hbound : 16 * staticMassBudget ≤ staticQueryLogConstant := by
    unfold staticQueryLogConstant
    linarith
  rw [show (dynamicSimulationAccuracy ε η)⁻¹ = 16 * staticMassBudget / (ε * η) by
    unfold dynamicSimulationAccuracy; field_simp]
  exact Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hbound (by positivity))

/-- The chosen Dyson degree is bounded by the dynamic degree constant times the sum of the
time-scale and accuracy logarithms. -/
theorem dynamicChosen_degree_bound {α T ε η : ℝ}
    (hα : 0 ≤ α) (hT : 0 ≤ T) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    let S := dynamicSegmentCount (staticKernelNormalization α (staticAnalyticBudget ε η)) T
    let ζ := dynamicSimulationAccuracy ε η
    (dynamicDysonDegree S ζ : ℝ) ≤
      dynamicDegreeConstant * (Real.log (2 + α * T) +
        Real.log (staticQueryLogConstant / (ε * η))) := by
  (try dsimp only)
  let S := dynamicSegmentCount (staticKernelNormalization α (staticAnalyticBudget ε η)) T
  let ζ := dynamicSimulationAccuracy ε η
  let ℓ := Real.log (staticQueryLogConstant / (ε * η))
  have hΛ : 0 ≤ staticKernelNormalization α (staticAnalyticBudget ε η) := by
    unfold staticKernelNormalization
    exact mul_nonneg hα (by linarith [staticKernelFrequencyBound_pos (staticAnalyticBudget ε η)])
  have hS : 0 < S := (dynamicSegmentCount_bounds hΛ hT).1
  have hSr : 0 < (S:ℝ) := by exact_mod_cast hS
  have hζ := dynamicSimulationAccuracy_bounds hε hε1 hη hη1
  have hK := dynamicDysonDegree_log_bound hS hζ.1 hζ.2.1
  have hℓ := (staticChosen_log_bound ε η hε hε1 hη hη1).1
  change 1 ≤ ℓ at hℓ
  have hℓpos : 0 < ℓ := by linarith
  have hX : 0 < 1 + α * T := by positivity
  have hY : 0 ≤ Real.log (2 + α * T) := Real.log_nonneg (by nlinarith)
  have hlogS : Real.log (S:ℝ) ≤ Real.log 15 + Real.log (2 + α * T) + ℓ := by
    have hm := Real.log_le_log hSr (dynamicChosen_segments_bound hα hT hε hε1 hη hη1)
    change Real.log (S:ℝ) ≤ Real.log (15 * (1 + α*T) * ℓ) at hm
    rw [Real.log_mul (by positivity : 15 * (1 + α*T) ≠ 0) hℓpos.ne',
      Real.log_mul (by norm_num : (15:ℝ) ≠ 0) hX.ne'] at hm
    have hx := Real.log_le_log hX (show 1 + α*T ≤ 2 + α*T by linarith)
    have hl := Real.log_le_self hℓpos.le
    linarith
  have hlogζ : Real.log ζ⁻¹ ≤ ℓ := dynamic_inverse_precision_log_le hε hη
  have he : Real.log (20 * (S:ℝ)^2 / ζ^2) =
      Real.log 20 + 2 * Real.log (S:ℝ) + 2 * Real.log ζ⁻¹ := by
    rw [Real.log_div (by positivity : 20 * (S:ℝ)^2 ≠ 0)
        (by have := hζ.1; positivity : ζ^2 ≠ 0),
      Real.log_mul (by norm_num : (20:ℝ) ≠ 0) (by positivity : (S:ℝ)^2 ≠ 0),
      Real.log_pow, Real.log_pow, Real.log_inv]
    ring
  have hnum : Real.log (20 * (S:ℝ)^2 / ζ^2) ≤
      Real.log 20 + 2 * Real.log 15 + 2 * Real.log (2 + α*T) + 4 * ℓ := by
    rw [he]
    linarith
  have hd : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 ≤ Real.log 20 + 2 * Real.log 15 := by
    have := Real.log_pos (by norm_num : (1:ℝ) < 20)
    have := Real.log_pos (by norm_num : (1:ℝ) < 15)
    linarith
  have hbudget : Real.log 20 + 2 * Real.log 15 + 2 * Real.log (2 + α*T) + 4 * ℓ ≤
      (Real.log 20 + 2 * Real.log 15 + 6) * (Real.log (2 + α*T) + ℓ) := by
    have hm := mul_nonneg hC (show 0 ≤ Real.log (2 + α*T) + ℓ - 1 by linarith)
    nlinarith
  calc
    _ ≤ Real.log (20 * (S:ℝ)^2 / ζ^2) / Real.log 2 + 1 := hK
    _ ≤ ((Real.log 20 + 2 * Real.log 15 + 6) *
        (Real.log (2 + α*T) + ℓ)) / Real.log 2 + 1 := by
      have hv := (div_le_div_iff_of_pos_right hd).mpr (hnum.trans hbudget)
      linarith
    _ ≤ dynamicDegreeConstant * (Real.log (2 + α*T) + ℓ) := by
      unfold dynamicDegreeConstant
      have hh : 1 ≤ Real.log (2 + α*T) + ℓ := by linarith
      calc
        _ ≤ ((Real.log 20 + 2 * Real.log 15 + 6) *
            (Real.log (2 + α*T) + ℓ)) / Real.log 2 + (Real.log (2 + α*T) + ℓ) := by linarith
        _ = _ := by ring

/-- The product of the chosen segment count and Dyson degree satisfies the displayed bound
involving `1 + α * T` and two logarithmic factors. -/
theorem dynamicChosen_segment_degree_product_bound {α T ε η : ℝ}
    (hα : 0 ≤ α) (hT : 0 ≤ T) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    let S := dynamicSegmentCount (staticKernelNormalization α (staticAnalyticBudget ε η)) T
    let ζ := dynamicSimulationAccuracy ε η
    ((S * dynamicDysonDegree S ζ : ℕ) : ℝ) ≤
      15 * dynamicDegreeConstant * (1 + α * T) *
        Real.log (staticQueryLogConstant / (ε * η)) *
        (Real.log (2 + α * T) + Real.log (staticQueryLogConstant / (ε * η))) := by
  (try dsimp only)
  rw [Nat.cast_mul]
  have hs := dynamicChosen_segments_bound hα hT hε hε1 hη hη1
  have hk := dynamicChosen_degree_bound hα hT hε hε1 hη hη1
  (try dsimp only at hk)
  have hℓ := (staticChosen_log_bound ε η hε hε1 hη hη1).1
  have h := mul_le_mul hs hk (by positivity) (by positivity)
  convert! h using 1
  ring

/-- The chosen segment-degree product satisfies the displayed bound with accuracy logarithm `log
(2 / (ε * η))`. -/
theorem dynamicChosen_paper_product_bound {α T ε η : ℝ}
    (hα : 0 ≤ α) (hT : 0 ≤ T) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    let S := dynamicSegmentCount (staticKernelNormalization α (staticAnalyticBudget ε η)) T
    let ζ := dynamicSimulationAccuracy ε η
    ((S * dynamicDysonDegree S ζ : ℕ) : ℝ) ≤
      (15 * dynamicDegreeConstant * staticPaperLogFactor ^ 2) * (1 + α * T) *
        Real.log (2 / (ε * η)) * (Real.log (2 + α * T) + Real.log (2 / (ε * η))) := by
  (try dsimp only)
  have h := dynamicChosen_segment_degree_product_bound hα hT hε hε1 hη hη1
  (try dsimp only at h)
  let ℓ := Real.log (staticQueryLogConstant / (ε * η))
  let l := Real.log (2 / (ε * η))
  let y := Real.log (2 + α * T)
  have hℓ : 0 ≤ ℓ := by have := (staticChosen_log_bound ε η hε hε1 hη hη1).1; dsimp [ℓ]; linarith
  have hy : 0 ≤ y := Real.log_nonneg (by nlinarith)
  have hl : 0 ≤ l := by
    apply Real.log_nonneg
    apply (le_div_iff₀ (mul_pos hε hη)).mpr
    have hp : ε * η ≤ 1 := by nlinarith
    linarith
  have hA : 1 ≤ staticPaperLogFactor := by
    unfold staticPaperLogFactor
    have hd : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have := div_nonneg (abs_nonneg (Real.log (staticQueryLogConstant / 2))) hd.le
    linarith
  have hL : ℓ ≤ staticPaperLogFactor * l := staticChosen_log_paper_bound ε η hε hε1 hη hη1
  have hYL : y + ℓ ≤ staticPaperLogFactor * (y + l) := by
    have := mul_nonneg (show 0 ≤ staticPaperLogFactor - 1 by linarith) hy
    nlinarith
  have hm :=
      mul_le_mul hL hYL (by linarith : 0 ≤ y + ℓ) (by positivity : 0 ≤ staticPaperLogFactor * l)
  have hc : 0 ≤ 15 * dynamicDegreeConstant * (1 + α * T) := by
    have := dynamicDegreeConstant_pos
    positivity
  have hb := mul_le_mul_of_nonneg_left hm hc
  apply h.trans
  convert! hb using 1 <;> dsimp only [ℓ,l,y] <;> ring

/-- Defines the dynamic paper query constant by combining segment, amplification, degree, and
logarithm comparison factors. -/
def dynamicPaperQueryConstant : ℝ :=
  15 * (4 * staticMassBudget + 1) * dynamicDegreeConstant * staticPaperLogFactor ^ 2

/-- The dynamic paper query constant is positive. -/
theorem dynamicPaperQueryConstant_pos : 0 < dynamicPaperQueryConstant := by
  have hC := staticMassBudget_ge_one
  have hD := dynamicDegreeConstant_pos
  have hF : 0 < staticPaperLogFactor := by
    unfold staticPaperLogFactor
    have hd : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  unfold dynamicPaperQueryConstant
  positivity

/-- The amplified segment-degree cost, scaled by any nonnegative `q`, is bounded by the
displayed dynamic query expression [WangEtAl2026]. -/
theorem dynamicChosen_amplified_query_bound {α T ε η q : ℝ}
    (hα : 0 ≤ α) (hT : 0 ≤ T) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hη : 0 < η) (hη1 : η ≤ 1) (hq : 0 ≤ q) :
    let S := dynamicSegmentCount (staticKernelNormalization α (staticAnalyticBudget ε η)) T
    let ζ := dynamicSimulationAccuracy ε η
    ((4 * staticMassBudget + 1) / η) * q * ((S * dynamicDysonDegree S ζ : ℕ) : ℝ) ≤
      (q * dynamicPaperQueryConstant) * ((1 + α * T) / η) *
        Real.log (2 / (ε * η)) * (Real.log (2 + α * T) + Real.log (2 / (ε * η))) := by
  (try dsimp only)
  have h := dynamicChosen_paper_product_bound hα hT hε hε1 hη hη1
  (try dsimp only at h)
  have hc : 0 ≤ ((4 * staticMassBudget + 1) / η) * q := by
    have := staticMassBudget_ge_one
    positivity
  convert! mul_le_mul_of_nonneg_left h hc using 1
  unfold dynamicPaperQueryConstant
  ring

/-- If the true output norm `ν` lies between `η` and `c * η`, the query expression based on `η`
is bounded by the one based on `ν` with factor `c * (outputEstimateLogFactor c)^2`. -/
theorem dynamic_true_output_query_bound {α T ε η ν c Q : ℝ}
    (hα : 0 ≤ α) (hT : 0 ≤ T) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hη : 0 < η) (hην : η ≤ ν) (hνc : ν ≤ c * η) (hc : 1 ≤ c)
    (hν1 : ν ≤ 1) (hQ : 0 ≤ Q) :
    Q * ((1 + α*T)/η) * Real.log (2/(ε*η)) *
      (Real.log (2+α*T) + Real.log (2/(ε*η))) ≤
    (Q * c * outputEstimateLogFactor c ^ 2) * ((1 + α*T)/ν) *
      Real.log (2/(ε*ν)) * (Real.log (2+α*T) + Real.log (2/(ε*ν))) := by
  have hν : 0 < ν := hη.trans_le hην
  have hη1 : η ≤ 1 := hην.trans hν1
  have hFp := outputEstimateLogFactor_pos hc
  have hF : 1 ≤ outputEstimateLogFactor c := by
    unfold outputEstimateLogFactor
    have := div_nonneg (Real.log_nonneg hc) (Real.log_pos (by norm_num : (1:ℝ) < 2)).le
    linarith
  have hy : 0 ≤ Real.log (2+α*T) := Real.log_nonneg (by nlinarith)
  have hlη : 0 ≤ Real.log (2/(ε*η)) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ (mul_pos hε hη)).mpr
    have hp : ε*η ≤ 1 := by nlinarith
    linarith
  have hlν : 0 ≤ Real.log (2/(ε*ν)) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ (mul_pos hε hν)).mpr
    have hp : ε*ν ≤ 1 := by nlinarith
    linarith
  have hlog := output_estimate_log_bound hη hην hνc hc hν1 hε hε1
  have hsum : Real.log (2+α*T) + Real.log (2/(ε*η)) ≤
      outputEstimateLogFactor c * (Real.log (2+α*T) + Real.log (2/(ε*ν))) := by
    have := mul_nonneg (show 0 ≤ outputEstimateLogFactor c - 1 by linarith) hy
    nlinarith
  have hinv := (output_estimate_envelope_bound hη hην hνc
    (show 0 ≤ 1 + α*T by positivity)).2
  have hfirst := mul_le_mul (mul_le_mul_of_nonneg_left hinv hQ) hlog hlη
    (show 0 ≤ Q * (c * ((1+α*T)/ν)) by
      have hc0 : 0 < c := by linarith
      positivity)
  have hsecond := mul_le_mul hfirst hsum (by positivity : 0 ≤ Real.log (2+α*T) + Real.log (2/(ε*η)))
    (show 0 ≤ Q * (c * ((1+α*T)/ν)) * (outputEstimateLogFactor c * Real.log (2/(ε*ν))) by
      have hc0 : 0 < c := by linarith
      positivity)
  convert! hsecond using 1
  ring

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
