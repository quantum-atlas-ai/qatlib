/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.StaticFinalQueryBudget

/-!
# Query Budgets from Output Norm Estimates

This module compares resource bounds expressed using a positive output norm estimate `η` with
bounds expressed using a true norm `ν`, under `η ≤ ν ≤ c * η`. Reciprocal factors lose at most
`c`, while `outputEstimateLogFactor` controls the accompanying logarithmic factors.

`static_true_output_query_bound` combines these comparisons for the static paper query envelope.
It replaces the estimated norm by the true output norm at the cost of the explicit multiplier `c
* outputEstimateLogFactor c`. See [WangEtAl2026].

## Main statements

* `output_estimate_inverse_bound` and `output_estimate_envelope_bound` compare inverse-norm
  factors.
* `output_estimate_log_bound` and `output_estimate_log_two_add_bound` compare logarithmic
  factors.
* `static_true_output_query_bound` transfers the complete static query envelope to the true
  norm.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

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

/-- The logarithmic comparison factor `1 + Real.log c / Real.log 2` used when replacing an
output norm estimate by a factor-`c` comparable norm. -/
def outputEstimateLogFactor (c : ℝ) : ℝ := 1 + Real.log c / Real.log 2

/-- The output-estimate logarithmic comparison factor is positive whenever `c ≥ 1`. -/
theorem outputEstimateLogFactor_pos {c : ℝ} (hc : 1 ≤ c) :
    0 < outputEstimateLogFactor c := by
  have hd : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := Real.log_nonneg hc
  unfold outputEstimateLogFactor
  positivity

/-- If the positive estimate `η` satisfies `η ≤ ν ≤ c * η`, then `1 / η` lies between `1 / ν`
and `c / ν`. -/
theorem output_estimate_inverse_bound {η ν c : ℝ}
    (hη : 0 < η) (hην : η ≤ ν) (hνc : ν ≤ c * η) :
    1 / ν ≤ 1 / η ∧ 1 / η ≤ c / ν := by
  have hν : 0 < ν := hη.trans_le hην
  constructor
  · exact one_div_le_one_div_of_le hη hην
  · apply (div_le_div_iff₀ hη hν).mpr
    simpa only [one_mul] using! hνc

/-- For nonnegative `E` and `η ≤ ν ≤ c * η` with `η > 0`, the envelope `E / η` lies between `E /
ν` and `c * (E / ν)`. -/
theorem output_estimate_envelope_bound {η ν c E : ℝ}
    (hη : 0 < η) (hην : η ≤ ν) (hνc : ν ≤ c * η) (hE : 0 ≤ E) :
    E / ν ≤ E / η ∧ E / η ≤ c * (E / ν) := by
  obtain ⟨hl,hu⟩ := output_estimate_inverse_bound hη hην hνc
  constructor
  · simpa only [mul_one_div] using! mul_le_mul_of_nonneg_left hl hE
  · convert! mul_le_mul_of_nonneg_left hu hE using 1 <;> ring

/-- Bounds `Real.log (2 / (ε * η))` by `outputEstimateLogFactor c` times the corresponding
expression using `ν`, under the positive comparable-norm and unit-upper-bound assumptions. -/
theorem output_estimate_log_bound {η ν c ε : ℝ}
    (hη : 0 < η) (hην : η ≤ ν) (hνc : ν ≤ c * η) (hc : 1 ≤ c)
    (hν1 : ν ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Real.log (2 / (ε * η)) ≤
      outputEstimateLogFactor c * Real.log (2 / (ε * ν)) := by
  have hν : 0 < ν := hη.trans_le hην
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hd : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlc : 0 ≤ Real.log c := Real.log_nonneg hc
  have hr : 2 / (ε * η) ≤ c * (2 / (ε * ν)) := by
    have hi := (output_estimate_inverse_bound hη hην hνc).2
    convert! mul_le_mul_of_nonneg_left hi (show 0 ≤ 2 / ε by positivity) using 1 <;> ring
  have hmon := Real.log_le_log (show 0 < (2:ℝ) / (ε * η) by positivity) hr
  rw [Real.log_mul hc0.ne' (by positivity : (2:ℝ) / (ε * ν) ≠ 0)] at hmon
  have hbase : Real.log 2 ≤ Real.log (2 / (ε * ν)) := by
    apply Real.log_le_log (by norm_num)
    apply (le_div_iff₀ (mul_pos hε hν)).mpr
    have hp : ε * ν ≤ 1 := by nlinarith
    linarith
  have hm := mul_le_mul_of_nonneg_left hbase (div_nonneg hlc hd.le)
  rw [div_mul_cancel₀ _ hd.ne'] at hm
  unfold outputEstimateLogFactor
  nlinarith

/-- For nonnegative `x` and `y` with `x ≤ c * y` and `c ≥ 1`, bounds `Real.log (2 + x)` by
`outputEstimateLogFactor c * Real.log (2 + y)`. -/
theorem output_estimate_log_two_add_bound {x y c : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ c * y) (hy : 0 ≤ y) (hc : 1 ≤ c) :
    Real.log (2 + x) ≤ outputEstimateLogFactor c * Real.log (2 + y) := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hd : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlc : 0 ≤ Real.log c := Real.log_nonneg hc
  have hm := Real.log_le_log (show 0 < 2 + x by linarith)
    (show 2 + x ≤ c * (2 + y) by nlinarith)
  rw [Real.log_mul hc0.ne' (by positivity : (2:ℝ) + y ≠ 0)] at hm
  have hb := Real.log_le_log (by norm_num : (0:ℝ) < 2) (show 2 ≤ 2 + y by linarith)
  have hp := mul_le_mul_of_nonneg_left hb (div_nonneg hlc hd.le)
  rw [div_mul_cancel₀ _ hd.ne'] at hp
  unfold outputEstimateLogFactor
  nlinarith

/-- Replaces the positive estimated output norm `η` in the static query envelope by a true norm
`ν` satisfying `η ≤ ν ≤ c * η`. The resulting bound increases the constant by `c *
outputEstimateLogFactor c` under the stated scale, time, and accuracy assumptions. -/
theorem static_true_output_query_bound {α t ε η ν c : ℝ}
    (hα : 0 ≤ α) (ht : 0 ≤ t) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hη : 0 < η) (hην : η ≤ ν) (hνc : ν ≤ c * η) (hc : 1 ≤ c) (hν1 : ν ≤ 1) :
    staticPaperQueryConstant * ((1 + α * t) / η) * Real.log (2 / (ε * η)) ≤
      (staticPaperQueryConstant * c * outputEstimateLogFactor c) *
        ((1 + α * t) / ν) * Real.log (2 / (ε * ν)) := by
  have hν : 0 < ν := hη.trans_le hην
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hnum : 0 ≤ 1 + α * t := by positivity
  have hi := (output_estimate_envelope_bound hη hην hνc hnum).2
  have hl := output_estimate_log_bound hη hην hνc hc hν1 hε hε1
  have hη1 : η ≤ 1 := hην.trans hν1
  have hlog : 0 ≤ Real.log (2 / (ε * η)) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ (mul_pos hε hη)).mpr
    have hp : ε * η ≤ 1 := by nlinarith
    linarith
  have hs := mul_le_mul_of_nonneg_left hi staticPaperQueryConstant_pos.le
  have hb : 0 ≤ staticPaperQueryConstant * (c * ((1 + α * t) / ν)) := by
    have := staticPaperQueryConstant_pos
    positivity
  have h := mul_le_mul hs hl hlog hb
  convert! h using 1
  ring

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
