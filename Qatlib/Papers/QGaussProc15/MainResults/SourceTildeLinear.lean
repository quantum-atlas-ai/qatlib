/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QGaussProc15.MainResults.SourceCostModel

set_option backward.isDefEq.respectTransparency false

/-!
# QGaussProc15 c002 — `Õ(n)` when the training output `y` is dense

Zhao--Fitzsimons--Fitzsimons, fixed arXiv:1512.03929v1 (12 Dec 2015),
claim c002 (main text, "Discussion"): even if `y` cannot be replaced by a
sparse vector, the variance on the estimation of the linear predictor
scales only linearly in `n`, so the estimation must be repeated a linear
number of times to reach constant error, giving an algorithm that scales as
`Õ(n)`.

Formalisation.  With dense `y` the estimator variance is `v · n`
(`denseEstimatorVariance`).  Driving it to `ε²` needs
`R = v · n / ε²` runs (`repetitionsNeeded`), which is linear in `n`
(`repetitions_needed_scales_linearly`; `dense_variance_eq_repetitions_mul`
records that `R` runs reduce the variance exactly to `ε²`).  The total cost
`R · qlaRunCost C n` is `Õ(n)` in the precise sense `IsTildeLinear`: it is
`O(n^{1+δ})` for every `δ > 0` (`repeated_run_cost_isTildeLinear`).
-/

set_option autoImplicit false
noncomputable section

open Filter Asymptotics

namespace Qatlib.Papers.QGaussProc15.MainResults

/-- **Fixed arXiv:1512.03929v1 (c002), linear repetition count.**  The
number of independent runs needed for constant error, `v · n / ε²`, is
exactly proportional to `n`: the estimation must be repeated a linear
number of times. -/
theorem repetitions_needed_scales_linearly (v ε : ℝ) (_hε : ε ≠ 0) (n : ℕ) :
    repetitionsNeeded v ε n = (v / ε ^ 2) * n := by
  unfold repetitionsNeeded
  rw [div_eq_mul_inv]
  ring

/-- **Fixed arXiv:1512.03929v1 (c002).**  Running `R = v·n/ε²` independent
runs makes the estimator variance exactly `ε²`: `v·n = R · ε²`.  Together
with `repetitions_needed_scales_linearly` this is the source's "a linear
number of repetitions suffices for constant error". -/
theorem dense_variance_eq_repetitions_mul (v ε : ℝ) (hε : ε ≠ 0) (n : ℕ) :
    denseEstimatorVariance v n = repetitionsNeeded v ε n * ε ^ 2 := by
  unfold denseEstimatorVariance repetitionsNeeded
  rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hε), mul_one]

/-- **Fixed arXiv:1512.03929v1 (c002), `Õ(n)` total cost.**  With dense `y`
the total cost of the repeated QLA estimation, `R · qlaRunCost C n`, is
soft-linear `Õ(n)`: bounded by `n^{1+δ}` up to a constant for every
`δ > 0`. -/
theorem repeated_run_cost_isTildeLinear (v ε C : ℝ) (hε : 0 < ε) :
    IsTildeLinear (repeatedRunCost v ε C) := by
  intro δ hδ
  have hbase : (fun n : ℕ => (n : ℝ) * (Real.log ((n : ℝ) + 1)) ^ 2) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ (1 + δ) := n_mul_logSq_isLittleO_rpow δ hδ
  have hc := hbase.const_mul_left (v * C / ε ^ 2)
  refine hc.isBigO.congr_left ?_
  intro n
  unfold repeatedRunCost repetitionsNeeded qlaRunCost
  rw [div_eq_mul_inv]
  ring

end Qatlib.Papers.QGaussProc15.MainResults
