/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.CosineQueryBudget
import Qatlib.Papers.Cbmd26.Algorithms.OutputNormEstimateBudget

/-!
# Output-estimate comparisons for cosine query budgets

Measures the effect of replacing the output-norm parameter in `cosineRelativeEnvelope`. A factor
comparison of envelopes yields the explicit factor `cosineOutputDegreeFactor` for the displayed
polynomial degree and a corresponding source-query factor. These results support the
contour-based algorithms of [WangEtAl2026].

## Main statements

* `cosineDisplayedDegreeBound_ratio_compare`: bounds the change in displayed degree.
* `cosineDisplayedSourceBound_ratio_compare`: bounds the change in the source-query expression.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

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

/-- Defines the output-estimate degree factor as `c + outputEstimateLogFactor c`. -/
def cosineOutputDegreeFactor (c : ℝ) : ℝ := c + outputEstimateLogFactor c

/-- The output-estimate degree factor is at least one when `c ≥ 1`. -/
theorem cosineOutputDegreeFactor_ge_one {c : ℝ} (hc : 1 ≤ c) :
    1 ≤ cosineOutputDegreeFactor c := by
  unfold cosineOutputDegreeFactor
  linarith [outputEstimateLogFactor_pos hc]

/-- An envelope ratio at most `c` bounds the displayed degree ratio by `cosineOutputDegreeFactor
c` under the stated positivity conditions. -/
theorem cosineDisplayedDegreeBound_ratio_compare
    {L H γ τ ε η ν κ c : ℝ}
    (hL : 0 ≤ L) (hH : 0 ≤ H) (hγ : 0 ≤ γ) (hτ : 0 ≤ τ)
    (hε : 0 < ε) (hη : 0 < η) (hν : 0 < ν) (hκ : 0 ≤ κ) (hc : 1 ≤ c)
    (hR : cosineRelativeEnvelope γ τ η ≤ c * cosineRelativeEnvelope γ τ ν) :
    cosineDisplayedDegreeBound L H γ τ ε η κ ≤
      cosineOutputDegreeFactor c * cosineDisplayedDegreeBound L H γ τ ε ν κ := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hF0 := outputEstimateLogFactor_pos hc
  have hG := cosineOutputDegreeFactor_ge_one hc
  have hG0 : 0 ≤ cosineOutputDegreeFactor c := by linarith
  have hRcη : 0 ≤ cosineRelativeEnvelope γ τ η := by unfold cosineRelativeEnvelope; positivity
  have hRcν : 0 ≤ cosineRelativeEnvelope γ τ ν := by unfold cosineRelativeEnvelope; positivity
  have hlogA : 0 ≤ Real.log (2 + γ*τ^2) := Real.log_nonneg (by nlinarith [sq_nonneg τ])
  have hBν := cosineSelectedBmax_nonneg (γ := γ) (τ := τ) hL hH hε hν
  have hBη := cosineSelectedBmax_nonneg (γ := γ) (τ := τ) hL hH hε hη
  have hB : cosineSelectedBmax L H γ τ ε η ≤ c^2 * cosineSelectedBmax L H γ τ ε ν := by
    have hr := mul_le_mul_of_nonneg_left hR (show 0 ≤ 1352 * H / ε by positivity)
    have hl := mul_nonneg (show 0 ≤ c-1 by linarith) hL
    have hc2 : c ≤ c^2 := by nlinarith
    have hx := mul_le_mul_of_nonneg_right hc2 hBν
    have hterm : 1352 * H * cosineRelativeEnvelope γ τ η / ε ≤
        c * (1352 * H * cosineRelativeEnvelope γ τ ν / ε) := by
      convert! hr using 1 <;> ring
    unfold cosineSelectedBmax at hx ⊢
    nlinarith only [hterm,hl,hx]
  have hsq : Real.sqrt (2 * cosineSelectedBmax L H γ τ ε η) ≤
      c * Real.sqrt (2 * cosineSelectedBmax L H γ τ ε ν) := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · rw [mul_pow, Real.sq_sqrt (by positivity)]
      nlinarith
  have hlog := output_estimate_log_two_add_bound
    (show 0 ≤ 1024 * cosineRelativeEnvelope γ τ η * Real.log (2+γ*τ^2) / ε by positivity)
    (show 1024 * cosineRelativeEnvelope γ τ η * Real.log (2+γ*τ^2) / ε ≤
      c * (1024 * cosineRelativeEnvelope γ τ ν * Real.log (2+γ*τ^2) / ε) by
        have := mul_le_mul_of_nonneg_right hR
          (show 0 ≤ 1024 * Real.log (2+γ*τ^2) / ε by positivity)
        convert! this using 1 <;> ring)
    (show 0 ≤ 1024 * cosineRelativeEnvelope γ τ ν * Real.log (2+γ*τ^2) / ε by positivity) hc
  have hlogν : 0 ≤ Real.log (2 + 1024 * cosineRelativeEnvelope γ τ ν * Real.log (2+γ*τ^2) / ε) :=
    Real.log_nonneg (by
      have hx : 0 ≤ 1024 * cosineRelativeEnvelope γ τ ν * Real.log (2+γ*τ^2) / ε := by positivity
      linarith)
  have hrootν : 0 ≤ τ * Real.sqrt (2 * cosineSelectedBmax L H γ τ ε ν) := by positivity
  have htime := mul_le_mul_of_nonneg_left hsq hτ
  have hco : c ≤ cosineOutputDegreeFactor c := by unfold cosineOutputDegreeFactor; linarith
  have hfo : outputEstimateLogFactor c ≤ cosineOutputDegreeFactor c := by
    unfold cosineOutputDegreeFactor
    linarith
  have hnum : τ * Real.sqrt (2 * cosineSelectedBmax L H γ τ ε η) +
      Real.log (2+1024*cosineRelativeEnvelope γ τ η*Real.log (2+γ*τ^2)/ε) ≤
      cosineOutputDegreeFactor c *
        (τ * Real.sqrt (2 * cosineSelectedBmax L H γ τ ε ν) +
          Real.log (2+1024*cosineRelativeEnvelope γ τ ν*Real.log (2+γ*τ^2)/ε)) := by
    have ht := mul_le_mul_of_nonneg_right hco hrootν
    have hl := mul_le_mul_of_nonneg_right hfo hlogν
    nlinarith
  have hd : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv := (div_le_div_iff_of_pos_right hd).mpr hnum
  have hbr :
      (τ * Real.sqrt (2 * cosineSelectedBmax L H γ τ ε η) +
        Real.log (2+1024*cosineRelativeEnvelope γ τ η*Real.log (2+γ*τ^2)/ε)) / Real.log 2 + 1 ≤
      cosineOutputDegreeFactor c *
        ((τ * Real.sqrt (2 * cosineSelectedBmax L H γ τ ε ν) +
          Real.log (2+1024*cosineRelativeEnvelope γ τ ν*Real.log (2+γ*τ^2)/ε)) / Real.log 2 + 1) := by
    have heq : cosineOutputDegreeFactor c *
        (τ * Real.sqrt (2 * cosineSelectedBmax L H γ τ ε ν) +
          Real.log (2+1024*cosineRelativeEnvelope γ τ ν*Real.log (2+γ*τ^2)/ε)) / Real.log 2 =
        cosineOutputDegreeFactor c * ((τ * Real.sqrt (2 * cosineSelectedBmax L H γ τ ε ν) +
          Real.log (2+1024*cosineRelativeEnvelope γ τ ν*Real.log (2+γ*τ^2)/ε)) / Real.log 2) := by ring
    rw [heq] at hdiv
    nlinarith
  unfold cosineDisplayedDegreeBound
  convert! mul_le_mul_of_nonneg_right hbr (show 0 ≤ 5+2048*κ by positivity) using 1
  ring

/-- An envelope ratio at most `c` bounds the displayed source-query ratio by `c *
cosineOutputDegreeFactor c`. -/
theorem cosineDisplayedSourceBound_ratio_compare
    {L H γ τ ε η ν κ c : ℝ}
    (hL : 0 ≤ L) (hH : 0 ≤ H) (hγ : 0 ≤ γ) (hτ : 0 ≤ τ)
    (hε : 0 < ε) (hη : 0 < η) (hν : 0 < ν) (hκ : 0 ≤ κ) (hc : 1 ≤ c)
    (hR : cosineRelativeEnvelope γ τ η ≤ c * cosineRelativeEnvelope γ τ ν) :
    (112 * cosineRelativeEnvelope γ τ η * Real.log (2+γ*τ^2)) *
      (8 * cosineDisplayedDegreeBound L H γ τ ε η κ + 2) ≤
    (c * cosineOutputDegreeFactor c) *
      ((112 * cosineRelativeEnvelope γ τ ν * Real.log (2+γ*τ^2)) *
        (8 * cosineDisplayedDegreeBound L H γ τ ε ν κ + 2)) := by
  have hd := cosineDisplayedDegreeBound_ratio_compare hL hH hγ hτ hε hη hν hκ hc hR
  have hG := cosineOutputDegreeFactor_ge_one hc
  have hq : 8 * cosineDisplayedDegreeBound L H γ τ ε η κ + 2 ≤
      cosineOutputDegreeFactor c * (8 * cosineDisplayedDegreeBound L H γ τ ε ν κ + 2) := by nlinarith
  have hlog : 0 ≤ Real.log (2+γ*τ^2) := Real.log_nonneg (by nlinarith [sq_nonneg τ])
  have hRη : 0 ≤ cosineRelativeEnvelope γ τ η := by unfold cosineRelativeEnvelope; positivity
  have hRν : 0 ≤ cosineRelativeEnvelope γ τ ν := by unfold cosineRelativeEnvelope; positivity
  have hdη : 0 ≤ cosineDisplayedDegreeBound L H γ τ ε η κ := by
    unfold cosineDisplayedDegreeBound
    have hl : 0 ≤ Real.log (2+1024*cosineRelativeEnvelope γ τ η*Real.log (2+γ*τ^2)/ε) :=
      Real.log_nonneg (by
        have hx : 0 ≤ 1024*cosineRelativeEnvelope γ τ η*Real.log (2+γ*τ^2)/ε := by positivity
        linarith)
    have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hr : 112 * cosineRelativeEnvelope γ τ η * Real.log (2+γ*τ^2) ≤
      c * (112 * cosineRelativeEnvelope γ τ ν * Real.log (2+γ*τ^2)) := by
    have := mul_le_mul_of_nonneg_right hR (show 0 ≤ 112*Real.log (2+γ*τ^2) by positivity)
    nlinarith
  have hb := mul_le_mul hr hq (by positivity)
    (show 0 ≤ c * (112*cosineRelativeEnvelope γ τ ν*Real.log (2+γ*τ^2)) by
      have hc0 : 0 < c := by linarith
      positivity)
  convert! hb using 1
  ring

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
