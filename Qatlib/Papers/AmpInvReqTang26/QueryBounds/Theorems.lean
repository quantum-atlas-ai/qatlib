/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AmpInvReqTang26.ForwardHist.Bounds

/-!
# Forward-query bounds for ensemble distinguishing

Theorems 3.1 and 4.3 are expressed for actual forward-query algorithms and their
ensemble-averaged output probabilities. For `0 < eps < 1/2` and `q ≥ 1/eps^2`, the stated
success thresholds force at least `1/(12 * eps^2)` queries. This development supports the
treatment in [TangWright2025].

## Main statements

* `theorem31_estimation_query_lower_bound`: the lower bound at success `2/3`.
* `theorem43_amplification_query_lower_bound`: the twisted-task bound at success `5/6`.

## References

* [Tang and Wright, 2025][TangWright2025]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.AmpInvReqTang26.QueryBounds
open Qatlib.Papers.AmpInvReqTang26.AccessModel
open Qatlib.Papers.AmpInvReqTang26.ForwardHist

/-- For `0 < eps < 1/2` and `q ≥ 1/eps^2`, distinguishing success at least `2/3` requires at
least `1/(12 * eps^2)` forward queries [Tang and Wright, Theorem 3.1][TangWright2025]. -/
theorem theorem31_estimation_query_lower_bound {d anc q : ℕ} {eps : ℝ}
    (he0 : 0<eps) (he1 : eps<1/2) (hq : 1/eps^2≤(q:ℝ))
    (Alg : ForwardQueryAlgorithm d anc) (n : ℕ)
    (hsucc : (2/3:ℝ) ≤ successProb q (one_div_sq_pos_cast he0 hq) eps he0.le (by linarith) Alg n) :
    1/(12*eps^2)≤(n:ℝ) := actual_source_query_lower_bound eps he0 he1 hq Alg n hsucc

/-- For `0 < eps < 1/2` and `q ≥ 1/eps^2`, success at least `5/6` in Problem 4.1 requires at
least `1/(12 * eps^2)` forward queries [Tang and Wright, Theorem 4.3][TangWright2025]. -/
theorem theorem43_amplification_query_lower_bound {d anc q : ℕ} {eps : ℝ}
    (he0 : 0<eps) (he1 : eps<1/2) (hq : 1/eps^2≤(q:ℝ))
    (Alg : ForwardQueryAlgorithm d anc) (n : ℕ)
    (hsucc : (5/6:ℝ) ≤ problem41Success q (one_div_sq_pos_cast he0 hq) eps he0.le (by linarith) Alg n) :
    1/(12*eps^2)≤(n:ℝ) := actual_source_twist_lower_bound eps he0 he1 hq Alg n hsucc

end Qatlib.Papers.AmpInvReqTang26.QueryBounds
