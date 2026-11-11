/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.StaticExponentialBridge

/-!
# Static exponential degree and source-query bounds

This module converts the dyadic truncation order for the oscillatory exponential into explicit
logarithmic degree and source-query estimates. These estimates feed the static CBMD cost
analysis of [WangEtAl2026].

## Main statements

* `static_exponential_degree_budget`: bounds the dyadic degree by a linear frequency term and a
  logarithmic error term.
* `static_exponential_source_query_budget`: gives the corresponding source-query bound.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SignalPrimitive.HermitianQSVT
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
noncomputable section
namespace CBMD

/-- For `0 < ε ≤ 1`, the static exponential's dyadic order is at most `(2 * |τ| + Real.log (4 /
ε)) / Real.log 2 + 1`. -/
theorem static_exponential_degree_budget (τ ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (dyadicOrder ((ε / 2) / (2 * Real.exp (2 * |τ|))) : ℝ) ≤
      (2 * |τ| + Real.log (4 / ε)) / Real.log 2 + 1 := by
  have hM : 1 ≤ Real.exp (2 * |τ|) := Real.one_le_exp (by positivity)
  have hi : ((ε / 2) / (2 * Real.exp (2 * |τ|)))⁻¹ =
      4 * Real.exp (2 * |τ|) / ε := by field_simp; norm_num
  have hr : 1 ≤ 4 * Real.exp (2 * |τ|) / ε :=
    (le_div_iff₀ hε).mpr (by nlinarith)
  have hn : 0 ≤ Real.log (4 * Real.exp (2 * |τ|) / ε) / Real.log 2 :=
    div_nonneg (Real.log_nonneg hr) (Real.log_pos (by norm_num)).le
  have hl : Real.log (4 * Real.exp (2 * |τ|) / ε) =
      2 * |τ| + Real.log (4 / ε) := by
    rw [show 4 * Real.exp (2 * |τ|) / ε = (4 / ε) * Real.exp (2 * |τ|) by ring,
      Real.log_mul (by positivity : (4 : ℝ) / ε ≠ 0) (Real.exp_ne_zero _), Real.log_exp]
    ring
  unfold dyadicOrder
  rw [hi]
  exact (Nat.ceil_lt_add_one hn).le.trans_eq (by rw [hl])

/-- For `0 < ε ≤ 1`, the static exponential source-query count is at most `16 * (2 * |τ| +
Real.log (4 / ε)) / Real.log 2 + 24`. -/
theorem static_exponential_source_query_budget (τ ε : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ((8 * (2 * dyadicOrder ((ε / 2) / (2 * Real.exp (2 * |τ|))) + 1) : ℕ) : ℝ) ≤
      16 * (2 * |τ| + Real.log (4 / ε)) / Real.log 2 + 24 := by
  have h := static_exponential_degree_budget τ ε hε hε1
  push_cast
  calc
    _ ≤ 8 * (2 * ((2 * |τ| + Real.log (4 / ε)) / Real.log 2 + 1) + 1) := by
      linarith
    _ = _ := by ring

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
