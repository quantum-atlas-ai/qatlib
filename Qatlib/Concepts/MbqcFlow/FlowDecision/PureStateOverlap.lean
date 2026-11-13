/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedFidelity.FidelityMetric.RankOneTraceNormBound
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge

/-!
# Trace distance from pure-state overlap

Proves `pure_traceDistance_le_of_inner`, which converts a lower bound on the real inner product
of two normalized vectors into a trace-distance bound for their outer products.

This estimate connects vector overlap and distinguishability of pure states, within the
trace-distance framework of [Watrous2018].

## Main statements

* `pure_traceDistance_le_of_inner`: a real-overlap deficit `ε` gives trace distance at most
  `sqrt (2 * ε)`.

## References

* [Watrous, 2018][Watrous2018]
-/

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.MixedFidelity.FidelityMetric
open Qatlib.Foundations.PureStateMath.Reflection

set_option autoImplicit false

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

open scoped BigOperators

/-- For normalized vectors with real inner product at least `1 - ε`, half the trace norm of the
difference of their outer products is at most `sqrt (2 * ε)`. -/
theorem pure_traceDistance_le_of_inner
    {I : Type*} [Fintype I] [DecidableEq I] (u v : QState I)
    (hu : Normalized u) (hv : Normalized v) (ε : ℝ)
    (hinner : 1 - ε ≤ (Inner u v).re) :
    (1 / 2 : ℝ) * (outerProduct u - outerProduct v).traceNorm ≤ Real.sqrt (2 * ε) := by
  have huN : (∑ i, Complex.normSq (u i)) = 1 := by
    simpa only [Complex.normSq_eq_norm_sq, Normalized, BornProb] using hu
  have hvN : (∑ i, Complex.normSq (v i)) = 1 := by
    simpa only [Complex.normSq_eq_norm_sq, Normalized, BornProb] using hv
  have hcross (i : I) : (u i * (starRingEnd ℂ) (v i)).re =
      ((starRingEnd ℂ) (u i) * v i).re := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hmass : (∑ i, Complex.normSq ((u - v) i)) = 2 - 2 * (Inner u v).re := by
    simp only [Pi.sub_apply, Complex.normSq_sub]
    simp_rw [hcross]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      huN, hvN, ← Complex.re_sum, ← inner_apply]
    ring
  have hmass_le : (∑ i, Complex.normSq ((u - v) i)) ≤ 2 * ε := by
    rw [hmass]
    linarith
  have heq : outerProduct u - outerProduct v =
      Matrix.vecMulVec (u - v) (star u) + Matrix.vecMulVec v (star (u - v)) := by
    ext i j
    simp only [outerProduct_apply, Matrix.sub_apply, Matrix.add_apply,
      Matrix.vecMulVec_apply, Pi.sub_apply, Pi.star_apply, star_sub, Complex.star_def]
    ring
  have hfirst := traceNorm_rankOne_le (u - v) u
  have hsecond := traceNorm_rankOne_le v (u - v)
  rw [huN, mul_one] at hfirst
  rw [hvN, one_mul] at hsecond
  have htriangle : (outerProduct u - outerProduct v).traceNorm ≤
      2 * Real.sqrt (∑ i, Complex.normSq ((u - v) i)) := by
    rw [heq]
    have ht := Matrix.traceNorm_add_le
      (Matrix.vecMulVec (u - v) (star u)) (Matrix.vecMulVec v (star (u - v)))
    linarith
  calc
    (1 / 2 : ℝ) * (outerProduct u - outerProduct v).traceNorm ≤
        Real.sqrt (∑ i, Complex.normSq ((u - v) i)) := by linarith
    _ ≤ Real.sqrt (2 * ε) := Real.sqrt_le_sqrt hmass_le

end Qatlib.Concepts.MbqcFlow.FlowDecision
