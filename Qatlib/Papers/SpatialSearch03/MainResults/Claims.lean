/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpatialSearch03.MainResults.SpectralAnalysis.TwoLevel
import Qatlib.Papers.SpatialSearch03.MainResults.SpectralAnalysis.EnergyBound
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Success probabilities and independent repetitions

This module evaluates the initial success probability of the uniform-state search model and
defines the repeated-trial expression `repeatedSuccessProbability`. Its bounds provide
elementary repetition estimates for the spatial-search analysis of [ChildsGoldstone2004].

## Main statements

* `repeated_success_ge_half`: If `p ≤ 1` and `k*p ≥ 1`, then the repeated-trial success
  expression is at least `1/2`.
* `repeatedSuccessProbability_mono`: For `0 ≤ p ≤ 1`, increasing the number of repetitions
  cannot decrease the repeated-trial success probability.

## References

* [Childs and Goldstone, 2004][ChildsGoldstone2004]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open scoped Classical BigOperators

namespace Qatlib.Papers.SpatialSearch03.MainResults.Claims

/-- The repeated-trial success expression `1 - (1-p)^k`, corresponding to at least one success
in `k` independent trials when `p` is a probability. -/
noncomputable def repeatedSuccessProbability (p : ℝ) (k : ℕ) : ℝ :=
  1 - (1 - p) ^ k

/-- At time zero, the search success probability is the reciprocal of the number of lattice
vertices. -/
theorem successProbability_zero (d n : ℕ) (γ : ℝ) (w : LatticeVertex d n) :
    successProbability d n γ w 0 = (Fintype.card (LatticeVertex d n) : ℝ)⁻¹ := by
  unfold successProbability
  rw [successAmplitude_zero, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (Fintype.card (LatticeVertex d n) : ℝ))]

/-- If `p ≤ 1` and `k*p ≥ 1`, then the repeated-trial success expression is at least `1/2`. See
[ChildsGoldstone2004]. -/
theorem repeated_success_ge_half (p : ℝ) (hp1 : p ≤ 1) (k : ℕ)
    (hk : 1 ≤ (k : ℝ) * p) : 1 / 2 ≤ repeatedSuccessProbability p k := by
  unfold repeatedSuccessProbability
  have hstep : 1 - p ≤ Real.exp (-p) := Real.one_sub_le_exp_neg p
  have h0 : 0 ≤ 1 - p := by linarith
  have h2 : (1 - p) ^ k ≤ (Real.exp (-p)) ^ k := pow_le_pow_left₀ h0 hstep k
  have h3 : (Real.exp (-p)) ^ k = Real.exp (-((k : ℝ) * p)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have h4 : Real.exp (-((k : ℝ) * p)) ≤ Real.exp (-1) := by
    apply Real.exp_le_exp.mpr
    linarith
  have h5 : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) (le_of_lt Real.exp_one_gt_two)
  have h6 : (1 - p) ^ k ≤ 1 / 2 := h2.trans (h3.trans_le (h4.trans h5))
  linarith

/-- For `0 ≤ p ≤ 1`, increasing the number of repetitions cannot decrease the repeated-trial
success probability. See [ChildsGoldstone2004]. -/
theorem repeatedSuccessProbability_mono (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {k l : ℕ} (hkl : k ≤ l) :
    repeatedSuccessProbability p k ≤ repeatedSuccessProbability p l := by
  unfold repeatedSuccessProbability
  have h0 : 0 ≤ 1 - p := by linarith
  have hle : 1 - p ≤ 1 := by linarith
  have h := pow_le_pow_of_le_one h0 hle hkl
  linarith

end Qatlib.Papers.SpatialSearch03.MainResults.Claims
