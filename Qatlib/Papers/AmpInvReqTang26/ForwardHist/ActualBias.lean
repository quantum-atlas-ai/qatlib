/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AmpInvReqTang26.ForwardHist.RawPurifications
import Qatlib.Papers.AmpInvReqTang26.BiasedFourier.UnbiasedGram

/-!
# Biased output domination and query lower bounds

Identifies the unbiased circuit density with a reduced histogram purification. For `n < q` and
`0 < eps < 1/2`, the biased output dominates `(1 - 4 * n * eps^2)` times the unbiased output,
yielding trace-distance and Born-success bounds.

The success bound gives `n ≥ 1 / (12 * eps^2)` whenever the weighted ensemble distinguishing
success is at least two thirds and `q ≥ 1 / eps^2`. See [TangWright2025].

## Main statements

* `actual_weighted_domination`: positive semidefinite domination of the actual weighted output
  densities.
* `actual_weighted_born_bound`: success is at most `1/2 + 2 * n * eps^2` in the low-query
  regime.
* `actual_weighted_query_lower_bound`: the lower bound on the number of forward queries.

## References

* [Tang and Wright, 2025][TangWright2025]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexOrder
open Matrix
namespace Qatlib.Papers.AmpInvReqTang26.ForwardHist
open Qatlib.Papers.AmpInvReqTang26.AccessModel
open Qatlib.Papers.AmpInvReqTang26.BiasedFourier
open Qatlib.Foundations.MatrixAlgebra.FrameProject.Tensor
open Qatlib.Concepts.MixedFidelity.FidelityMetric.Purification
open Qatlib.Concepts.MixedFidelity.FidelityMetric.Domination

/-- For `q > 1` and `n < q`, the unbiased weighted circuit density equals the reduced density of
`histogramPurification0`. -/
theorem histogramPurification0_reduced {d a : ℕ} (q : ℕ) (hq : 1<q)
    (Alg : ForwardQueryAlgorithm d a) (n : ℕ) (hn : n<q) :
    weightedCircuitDensity 0 q Alg n=reduced (histogramPurification0 Alg n q hn) := by
  calc
    _ = reduced (rawHistogramPurification 0 Alg n q hn) :=
      (rawHistogramPurification_reduced 0 q hq (by norm_num) (by norm_num) Alg n hn).symm
    _ = _ := reduced_gram_transport (pathCoefficient Alg n) _ _
      (unbiased_histogram_gram (by omega) (pathHistogram Alg n q hn) (pathHistogram_injective Alg n q hn))

/-- For `q > 1`, `0 < eps < 1/2`, and `n < q`, the biased weighted circuit density minus `(1 - 4
* n * eps^2)` times the unbiased density is positive semidefinite. -/
theorem actual_weighted_domination {d a : ℕ} (eps : ℝ) (q : ℕ) (hq : 1<q)
    (he0 : 0<eps) (he1 : eps<1/2) (Alg : ForwardQueryAlgorithm d a)
    (n : ℕ) (hn : n<q) :
    (weightedCircuitDensity eps q Alg n - (((1-4*(n:ℝ)*eps^2:ℝ):ℂ) •
      weightedCircuitDensity 0 q Alg n)).PosSemidef := by
  have h := actual_histogram_domination eps q hq he0 he1 Alg n hn
  rw [histogramPurification_gram_transport,rawHistogramPurification_reduced eps q hq he0.le (by linarith),
    ← histogramPurification0_reduced q hq Alg n hn] at h
  exact h

/-- For `q > 1`, `0 < eps < 1/2`, and `n < q`, the trace distance between the unbiased and
biased weighted circuit densities is at most `4 * n * eps^2`. -/
theorem actual_weighted_trace_distance {d a : ℕ} (eps : ℝ) (q : ℕ) (hq : 1<q)
    (he0 : 0<eps) (he1 : eps<1/2) (Alg : ForwardQueryAlgorithm d a)
    (n : ℕ) (hn : n<q) :
    Matrix.traceNorm (weightedCircuitDensity 0 q Alg n-weightedCircuitDensity eps q Alg n)/2 ≤
      4*(n:ℝ)*eps^2 := by
  apply density_domination_distance
  · exact weightedCircuitDensity_posSemidef 0 q hq (by norm_num) (by norm_num) Alg n
  · exact weightedCircuitDensity_trace 0 q (by omega) (by norm_num) (by norm_num) Alg n
  · exact weightedCircuitDensity_trace eps q (by omega) he0.le (by linarith) Alg n
  · positivity
  · exact actual_weighted_domination eps q hq he0 he1 Alg n hn

/-- The equal-prior distinguishing success from the false-labeled Born mass of the unbiased
density and the true-labeled Born mass of the biased density. -/
def weightedSuccess {d a : ℕ} (eps : ℝ) (q : ℕ) (Alg : ForwardQueryAlgorithm d a) (n : ℕ) : ℝ :=
  (bornMass (weightedCircuitDensity 0 q Alg n) Alg.good false +
    bornMass (weightedCircuitDensity eps q Alg n) Alg.good true)/2

/-- For `q > 1`, `0 < eps < 1/2`, and `n < q`, the weighted distinguishing success is at most
`1/2 + 2 * n * eps^2`. -/
theorem actual_weighted_born_bound {d a : ℕ} (eps : ℝ) (q : ℕ) (hq : 1<q)
    (he0 : 0<eps) (he1 : eps<1/2) (Alg : ForwardQueryAlgorithm d a)
    (n : ℕ) (hn : n<q) : weightedSuccess eps q Alg n≤1/2+2*(n:ℝ)*eps^2 := by
  have h := density_domination_born_success (weightedCircuitDensity 0 q Alg n)
    (weightedCircuitDensity eps q Alg n)
    (weightedCircuitDensity_posSemidef 0 q hq (by norm_num) (by norm_num) Alg n)
    (weightedCircuitDensity_trace 0 q (by omega) (by norm_num) (by norm_num) Alg n)
    (weightedCircuitDensity_trace eps q (by omega) he0.le (by linarith) Alg n)
    (4*(n:ℝ)*eps^2) (by positivity) (actual_weighted_domination eps q hq he0 he1 Alg n hn) Alg.good
  dsimp only [weightedSuccess]
  nlinarith

/-- For `0 < eps < 1/2` and `q ≥ 1 / eps^2`, weighted distinguishing success at least two thirds
requires `n ≥ 1 / (12 * eps^2)` [Tang and Wright, Theorem 3.1][TangWright2025]. -/
theorem actual_weighted_query_lower_bound {d a q : ℕ} (eps : ℝ) (he0 : 0<eps)
    (he1 : eps<1/2) (hq : 1/eps^2≤(q:ℝ)) (Alg : ForwardQueryAlgorithm d a) (n : ℕ)
    (hsucc : (2/3:ℝ)≤weightedSuccess eps q Alg n) : 1/(12*eps^2)≤(n:ℝ) := by
  have he2 : 0<eps^2 := sq_pos_of_pos he0
  have hqp : 1≤(q:ℝ)*eps^2 := (div_le_iff₀ he2).mp hq
  have hq2 : 1<q := by
    by_contra h
    have hqn : q≤1 := by omega
    have hqr : (q:ℝ)≤1 := by exact_mod_cast hqn
    nlinarith
  by_cases hn : n<q
  · have hb := actual_weighted_born_bound eps q hq2 he0 he1 Alg n hn
    apply (div_le_iff₀ (by positivity : 0<12*eps^2)).mpr
    nlinarith
  · have hqn : (q:ℝ)≤n := by exact_mod_cast (by omega : q≤n)
    have hh : 1/(12*eps^2)≤1/eps^2 := by
      apply div_le_div_of_nonneg_left (by norm_num) he2
      nlinarith
    exact hh.trans (hq.trans hqn)

end Qatlib.Papers.AmpInvReqTang26.ForwardHist
