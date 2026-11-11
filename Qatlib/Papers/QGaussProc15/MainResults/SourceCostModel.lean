/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# QGaussProc15 — the QLA cost model

Zhao--Fitzsimons--Fitzsimons, fixed arXiv:1512.03929v1 (12 Dec 2015).

This file supplies the cost vocabulary used by the two main asymptotic
claims c001 and c002:

* `qlaRunCost C n` is the cost of one QLA run of the paper's procedure
  (page 5, "Discussion"; page 2, "the quantum algorithm scales as
  `poly(log n, 1/ε, s, κ)`"): `C · log²(n + 1)`, with the dependence on the
  condition number `κ`, the sparsity `s` and the precision `ε` packaged
  into the constant `C`.
* `classicalGPRCost n` is the classical cost of GPR training/prediction,
  `Θ(n³)` (forming and Cholesky-factorising the `n × n` matrix
  `K + σ_n² I`, followed by triangular solves).
* `repetitionsNeeded v ε n` (c002) is the number of independent runs needed
  to bring the estimator variance `v · n` down to `ε²`.
* `repeatedRunCost v ε C n` is the resulting total cost
  `R · qlaRunCost C n`, which c002 asserts is `Õ(n)`.

The analytic workhorses are the subpolynomial bound `log² x = o(x^p)`
(proved here from Mathlib's `isLittleO_log_rpow_atTop`) and its composed
version along `n ↦ n + 1`.
-/

set_option autoImplicit false
noncomputable section

open Filter Asymptotics

namespace Qatlib.Papers.QGaussProc15.MainResults

/-- The cost of one QLA run of the paper's procedure: `C · log²(n + 1)`,
where `C` absorbs the condition number, sparsity and precision dependence
and `n` is the number of training points. -/
def qlaRunCost (C : ℝ) (n : ℕ) : ℝ := C * (Real.log ((n : ℝ) + 1)) ^ 2

/-- The classical GPR cost `Θ(n³)`: forming and factorising the `n × n`
kernel matrix `K + σ_n² I`. -/
def classicalGPRCost (n : ℕ) : ℝ := (n : ℝ) ^ 3

/-- The estimator variance of the linear predictor when the training output
`y` is dense: it grows linearly in `n`, `v · n`, with baseline variance
`v` (source page 5, "the variance … will scale only linear in n"). -/
def denseEstimatorVariance (v : ℝ) (n : ℕ) : ℝ := v * n

/-- The number of independent runs needed to bring the estimator variance
`v · n` down to `ε²`: `R = v · n / ε²`. -/
def repetitionsNeeded (v ε : ℝ) (n : ℕ) : ℝ := v * n / ε ^ 2

/-- The total cost of `R` independent QLA runs, `R · qlaRunCost C n`. -/
def repeatedRunCost (v ε C : ℝ) (n : ℕ) : ℝ :=
  repetitionsNeeded v ε n * qlaRunCost C n

/-- `Õ(g)`, "soft big-O": `f` is bounded by `g` up to subpolynomial
factors, i.e. `f = O(g · n^δ)` for every `δ > 0`.  Here we spell it out
for `g(n) = n`, which is the `Õ(n)` of claim c002. -/
def IsTildeLinear (f : ℕ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → f =O[atTop] fun n : ℕ => (n : ℝ) ^ (1 + δ)

/-! ## The analytic bound `log² x = o(x^p)` -/

/-- `(log x)² = o(x^p)` for every `p > 0`: the square of the logarithm is
subpolynomial. -/
theorem logSq_isLittleO_rpow (p : ℝ) (hp : 0 < p) :
    (fun x : ℝ => (Real.log x) ^ 2) =o[atTop] (fun x : ℝ => x ^ p) := by
  have hp2 : (0 : ℝ) < p / 2 := by linarith
  have hbase : Real.log =o[atTop] fun x : ℝ => x ^ (p / 2) :=
    isLittleO_log_rpow_atTop hp2
  have hsq : (fun x : ℝ => (Real.log x) ^ 2) =o[atTop]
      fun x : ℝ => (x ^ (p / 2)) ^ 2 := hbase.pow (by norm_num)
  refine hsq.congr' (by filter_upwards with x; rfl) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [← Real.rpow_natCast (x ^ (p / 2)) 2, ← Real.rpow_mul hx.le]
  congr 1
  ring

/-- The same bound along the natural numbers, shifted by one:
`(log (n + 1))² = o(n^p)` for every `p > 0`. -/
theorem logSq_succ_isLittleO_rpow (p : ℝ) (hp : 0 < p) :
    (fun n : ℕ => (Real.log ((n : ℝ) + 1)) ^ 2) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ p := by
  have hk : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    Tendsto.atTop_add (C := (1 : ℝ)) tendsto_natCast_atTop_atTop tendsto_const_nhds
  have hcomp := (logSq_isLittleO_rpow p hp).comp_tendsto hk
  -- `((n:ℝ) + 1)^p = O(n^p)` because `n + 1 ≤ 2 n` for `n ≥ 1`.
  have hbigO : (fun n : ℕ => ((n : ℝ) + 1) ^ p) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ p := by
    refine IsBigO.of_bound (2 ^ p) ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnp : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have hle : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by nlinarith
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) p),
      Real.norm_of_nonneg (Real.rpow_nonneg hnp p)]
    calc ((n : ℝ) + 1) ^ p ≤ (2 * (n : ℝ)) ^ p :=
          Real.rpow_le_rpow (by positivity) hle hp.le
      _ = 2 ^ p * (n : ℝ) ^ p := Real.mul_rpow (by norm_num) hnp
  exact hcomp.trans_isBigO hbigO

/-- `n · (log (n + 1))² = o(n^{1+δ})` for every `δ > 0`: the repeated-run
cost with a linear repetition factor is still `Õ(n)`. -/
theorem n_mul_logSq_isLittleO_rpow (δ : ℝ) (hδ : 0 < δ) :
    (fun n : ℕ => (n : ℝ) * (Real.log ((n : ℝ) + 1)) ^ 2) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ (1 + δ) := by
  have hlog : (fun n : ℕ => (Real.log ((n : ℝ) + 1)) ^ 2) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ δ := logSq_succ_isLittleO_rpow δ hδ
  have hid : (fun n : ℕ => (n : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) ^ (1 : ℝ) :=
    (isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).congr_right
      (fun n => (Real.rpow_one (n : ℝ)).symm)
  have hmul := hlog.mul_isBigO hid
  refine hmul.congr' (by filter_upwards with n; ring) ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [← Real.rpow_add hn']
  congr 1
  ring

end Qatlib.Papers.QGaussProc15.MainResults
