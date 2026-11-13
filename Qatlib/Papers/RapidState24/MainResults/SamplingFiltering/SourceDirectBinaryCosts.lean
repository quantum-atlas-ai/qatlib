/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option backward.isDefEq.respectTransparency false

/-!
# Direct-sampling vs. binary-search query complexity for initial state preparation

This file formalizes the direct-sampling and binary-search query-complexity expressions and the
FeMoco `p ≲ 0.003` crossover of [Berry et al., 2024][BerryEtAl2024Rapid] (Section I.A, pp. 4–5,
Eqs. (1) and (3); Section V.A, pp. 18–20, Eqs. (65)–(71); Section VI.C, pp. 27–28, Eq. (127)):

* `linearised_delta_solution`: solution of the linearized per-sample confidence equation (Eq. (71)).
* `eq1_leading_form` and `direct_cost_eq`: leading-order direct-sampling query counts (Eqs. (1)
  and (69)).
* `binary_constant_about_sixteen` and `binary_sqrt_scaling_ratio`: prefactor comparison (`15.54`)
  and `O(√p)` overlap scaling of binary search (Eq. (3)).
* `binary_beats_direct_at_0003`: certified numerical crossover inequality showing that binary
  search requires fewer queries than direct sampling at the FeMoco parameters
  `(p = 0.003, q = 0.05, λ = 306, ε = 0.0016)`.

## Main statements

* `linearised_delta_solution`: closed-form solution for `δ` in Eq. (71).
* `eq1_leading_form`: equivalence of `(n λ / 2ε) ln(1 / δ)` and `directSamplingQueries` (Eq. (1)).
* `binary_sqrt_scaling_ratio`: `1 / √p` vs. `1 / p` scaling ratio.
* `binary_beats_direct_at_0003`: `binarySearchQueries 0.003 0.05 306 0.0016 ≤
  directSamplingQueries 0.003 0.05 306 0.0016`.

## References

* [Berry et al., 2024][BerryEtAl2024Rapid]
-/

namespace Qatlib.Papers.RapidState24.MainResults.SamplingFiltering

set_option autoImplicit false

/-! ## §1. Direct sampling -/

/-- Eq. (67), Section V.A, p. 19: with squared ground-state overlap `p`, two-sided confidence
level `1 - δ` per sample, and `n` samples, the probability of a large error is
`[1 - p(1 - δ/2)]^n + 1 - (1 - δ/2)^n`. -/
noncomputable def sampleFailure (p δ : ℝ) (n : ℕ) : ℝ :=
  (1 - p * (1 - δ / 2)) ^ n + 1 - (1 - δ / 2) ^ n

/-- Definitional expansion of `sampleFailure` (Eq. (67)). -/
theorem sampleFailure_eq (p δ : ℝ) (n : ℕ) :
    sampleFailure p δ n
      = (1 - p * (1 - δ / 2)) ^ n + 1 - (1 - δ / 2) ^ n := rfl

/-- Eq. (70), Section V.A, p. 19: linearizing `sampleFailure` about `δ = 0` gives
`(1 - p)^n + (δ n / 2) [1 + p (1 - p)^{n - 1}]`. -/
noncomputable def linearisedFailure (p δ : ℝ) (n : ℕ) : ℝ :=
  (1 - p) ^ n + δ * (n : ℝ) / 2 * (1 + p * (1 - p) ^ (n - 1))

/-- Solution of the linearized failure equation (Eq. (71), Section V.A, pp. 19–20). -/
theorem linearised_delta_solution (p δ q : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hden : 1 + p * (1 - p) ^ (n - 1) ≠ 0)
    (h : linearisedFailure p δ n = q) :
    δ = 2 * (q - (1 - p) ^ n) / ((n : ℝ) * (1 + p * (1 - p) ^ (n - 1))) := by
  unfold linearisedFailure at h
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn))
  rw [eq_div_iff (mul_ne_zero hnR hden)]
  nlinarith [h]

/-- Direct-sampling leading-order query count of Eq. (1), Section I.A, p. 4:
`λ ln(2/q) / (2 p ε) · ln[ln(2/q) / (p q)]`. -/
noncomputable def directSamplingQueries (p q lam ε : ℝ) : ℝ :=
  lam * Real.log (2 / q) / (2 * p * ε) * Real.log (Real.log (2 / q) / (p * q))

/-- **Eq. (1)** ([Berry et al., 2024][BerryEtAl2024Rapid], Section I.A, p. 4): with
`n = ln(2/q) / p` and `δ = p q / ln(2/q)`, the leading query count `(n λ / 2ε) ln(1/δ)` equals
`directSamplingQueries p q lam ε`. -/
theorem eq1_leading_form (p q lam ε : ℝ) (hp : 0 < p) (hq : 0 < q) (hq1 : q < 1)
    (hlam : 0 < lam) (hε : 0 < ε) :
    (Real.log (2 / q) / p) * lam / (2 * ε) *
        Real.log (1 / (p * q / Real.log (2 / q)))
      = directSamplingQueries p q lam ε := by
  unfold directSamplingQueries
  have h2q : 1 < 2 / q := by
    rw [lt_div_iff₀ hq]
    nlinarith
  have hL : 0 < Real.log (2 / q) := Real.log_pos h2q
  have hpq : 0 < p * q := mul_pos hp hq
  have harg : 1 / (p * q / Real.log (2 / q)) = Real.log (2 / q) / (p * q) := by
    field_simp [hL.ne', hpq.ne']
  rw [harg]
  field_simp [hp.ne', hq.ne', hlam.ne', hε.ne', hL.ne']

/-- Overall sampling cost Eq. (69), Section V.A, p. 19:
`(λ / (2 p ε)) ln(1/q) ln(1/δ)` with `n = ln(1/q) / p` samples. -/
noncomputable def directSamplingCost (p q lam ε δ : ℝ) : ℝ :=
  lam / (2 * p * ε) * Real.log (1 / q) * Real.log (1 / δ)

/-- Cost identity Eqs. (68)–(69), Section V.A, p. 19. -/
theorem direct_cost_eq (p q lam ε δ : ℝ) (hp : 0 < p) (_hq : 0 < q) (_hq1 : q < 1)
    (hε : 0 < ε) (_hδ : 0 < δ) :
    (Real.log (1 / q) / p) * lam / (2 * ε) * Real.log (1 / δ)
      = directSamplingCost p q lam ε δ := by
  unfold directSamplingCost
  field_simp [hp.ne', hε.ne']

/-- Leading-order per-sample phase-estimation query count `(λ / 2ε) ln(1/δ)` (Eq. (65), p. 18). -/
noncomputable def phaseEstimationCost (lam ε δ : ℝ) : ℝ :=
  lam / (2 * ε) * Real.log (1 / δ)

/-- Definitional expansion of `phaseEstimationCost` (Eq. (65)). -/
theorem phaseEstimationCost_eq (lam ε δ : ℝ) :
    phaseEstimationCost lam ε δ = lam / (2 * ε) * Real.log (1 / δ) := rfl

/-! ## §2. Binary search and the `p ≲ 0.003` crossover -/

/-- Binary-search query count of Eq. (3) / Eq. (127), Section I.A p. 4 and Section VI.C p. 27:
`7.77 λ / (√p ε) · ln(4 / √p) · ln(log_{√2}(λ / ε) / q)`. -/
noncomputable def binarySearchQueries (p q lam ε : ℝ) : ℝ :=
  7.77 * lam / (Real.sqrt p * ε) * Real.log (4 / Real.sqrt p) *
    Real.log (Real.log (lam / ε) / Real.log (Real.sqrt 2) / q)

/-- Change-of-base identity `ln √2 = ln 2 / 2` used in Eq. (3). -/
theorem log_sqrt_two : Real.log (Real.sqrt 2) = Real.log 2 / 2 := by
  rw [Real.log_sqrt (by norm_num)]

/-- Constant-factor ratio `7.77 / (1 / 2) = 15.54 ∈ (15, 16)` between binary search and direct
sampling ([Berry et al., 2024][BerryEtAl2024Rapid], Section I.A, pp. 4–5). -/
theorem binary_constant_about_sixteen :
    (7.77 : ℝ) / (1 / 2) = 15.54 ∧ (15 : ℝ) < 15.54 ∧ (15.54 : ℝ) < 16 := by
  norm_num

/-- Overlap prefactor ratio `(7.77 / √p) / (ln(2/q) / (2p)) = 15.54 √p / ln(2/q)` showing the
`O(√p)` improvement of binary search over direct sampling. -/
theorem binary_sqrt_scaling_ratio (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (hq1 : q < 1) :
    (7.77 / Real.sqrt p) / (Real.log (2 / q) / (2 * p))
      = 15.54 * Real.sqrt p / Real.log (2 / q) := by
  have hs : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp.le
  have hsp : Real.sqrt p ≠ 0 := (Real.sqrt_pos.2 hp).ne'
  have hL : Real.log (2 / q) ≠ 0 := by
    have : 1 < 2 / q := by
      rw [lt_div_iff₀ hq]
      nlinarith
    exact (Real.log_pos this).ne'
  field_simp [hsp, hL, hp.ne']
  nlinarith

/-- Certified crossover inequality ([Berry et al., 2024][BerryEtAl2024Rapid], Section I.A p. 5
and Section VI.C pp. 27–28, Fig. 13): at the FeMoco parameters `(λ = 306, ε = 0.0016, q = 0.05)`,
binary search requires fewer queries than direct sampling at `p = 0.003`. -/
theorem binary_beats_direct_at_0003 :
    binarySearchQueries 0.003 0.05 306 0.0016
      ≤ directSamplingQueries 0.003 0.05 306 0.0016 := by
  unfold binarySearchQueries directSamplingQueries
  have hlog2_gt := Real.log_two_gt_d9
  have hlog2_lt := Real.log_two_lt_d9
  have hlog3_gt := Real.log_three_gt_d9
  have hlog3_lt := Real.log_three_lt_d9
  have hlog5_gt := Real.log_five_gt_d9
  have hlog5_lt := Real.log_five_lt_d9
  have hlog2_pos : 0 < Real.log 2 := by linarith
  -- Lower bound on `√0.003`: `(547 / 10000)^2 = 299209 / 100000000 < 0.003`
  have hsqrt_gt : (547 : ℝ) / 10000 < Real.sqrt 0.003 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 547 / 10000)]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hsqrt_pos : 0 < Real.sqrt 0.003 := by linarith
  -- Upper bound on `log (4 / √0.003) < log 75 = log 3 + 2 log 5 < 4.32`
  have h4div_lt : 4 / Real.sqrt 0.003 < 75 := by
    have h1 : 4 / Real.sqrt 0.003 < 4 / (547 / 10000) :=
      div_lt_div_of_pos_left (by norm_num) (by norm_num) hsqrt_gt
    linarith
  have hlog75 : Real.log (75 : ℝ) = Real.log 3 + 2 * Real.log 5 := by
    have h75 : (75 : ℝ) = 3 * 5 ^ 2 := by norm_num
    rw [h75, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have hlog_4sqrt_lt : Real.log (4 / Real.sqrt 0.003) < 4.32 := by
    have h1 : Real.log (4 / Real.sqrt 0.003) < Real.log 75 :=
      Real.log_lt_log (by positivity) h4div_lt
    linarith
  -- Upper bound on `log (log (306 / 0.0016) / log (√2) / 0.05) < log 720 < 6.58`
  have hlog_ratio_lt : Real.log ((306 : ℝ) / 0.0016) < 18 * Real.log 2 := by
    have h191 : (306 : ℝ) / 0.0016 = 191250 := by norm_num
    rw [h191]
    have hlt : (191250 : ℝ) < (2 : ℝ) ^ (18 : ℕ) := by norm_num
    have h1 := Real.log_lt_log (by norm_num) hlt
    rw [Real.log_pow] at h1
    norm_num at h1
    exact h1
  have hinner_bin_lt : Real.log ((306 : ℝ) / 0.0016) / Real.log (Real.sqrt 2) / 0.05 < 720 := by
    rw [log_sqrt_two]
    have hdiv : Real.log ((306 : ℝ) / 0.0016) / (Real.log 2 / 2) / 0.05 =
        40 * (Real.log ((306 : ℝ) / 0.0016) / Real.log 2) := by
      field_simp [hlog2_pos.ne']
      ring
    rw [hdiv]
    have hq : Real.log ((306 : ℝ) / 0.0016) / Real.log 2 < 18 :=
      (div_lt_iff₀ hlog2_pos).mpr hlog_ratio_lt
    linarith
  have hinner_bin_pos : 0 < Real.log ((306 : ℝ) / 0.0016) / Real.log (Real.sqrt 2) / 0.05 := by
    have hgt1 : (1 : ℝ) < (306 : ℝ) / 0.0016 := by norm_num
    have hlpos : 0 < Real.log ((306 : ℝ) / 0.0016) := Real.log_pos hgt1
    have hlsqrt : 0 < Real.log (Real.sqrt 2) := by
      rw [log_sqrt_two]
      linarith
    positivity
  have hlog720 : Real.log (720 : ℝ) = 4 * Real.log 2 + 2 * Real.log 3 + Real.log 5 := by
    have h720 : (720 : ℝ) = 2 ^ 4 * 3 ^ 2 * 5 := by norm_num
    rw [h720, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    norm_num
  have hlog_bin2_lt :
      Real.log (Real.log ((306 : ℝ) / 0.0016) / Real.log (Real.sqrt 2) / 0.05) < 6.58 := by
    have h1 := Real.log_lt_log hinner_bin_pos hinner_bin_lt
    linarith
  -- Lower bound on `log (2 / 0.05) = log 40 = 3 log 2 + log 5 > 3.688`
  have hlog40 : Real.log ((2 : ℝ) / 0.05) = 3 * Real.log 2 + Real.log 5 := by
    have h40 : (2 : ℝ) / 0.05 = 2 ^ 3 * 5 := by norm_num
    rw [h40, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have hlog40_gt : 3.688 < Real.log ((2 : ℝ) / 0.05) := by linarith
  -- Lower bound on `log (log (2 / 0.05) / (0.003 * 0.05)) > log 24000 > 10.08`
  have h24000_lt : (24000 : ℝ) < Real.log ((2 : ℝ) / 0.05) / (0.003 * 0.05) := by
    rw [lt_div_iff₀ (by norm_num)]
    linarith
  have hlog24000 : Real.log (24000 : ℝ) = 6 * Real.log 2 + Real.log 3 + 3 * Real.log 5 := by
    have h24k : (24000 : ℝ) = 2 ^ 6 * 3 * 5 ^ 3 := by norm_num
    rw [h24k, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    norm_num
  have hlog_dir2_gt : 10.08 < Real.log (Real.log ((2 : ℝ) / 0.05) / (0.003 * 0.05)) := by
    have h1 := Real.log_lt_log (by norm_num) h24000_lt
    linarith
  -- Combine into numerical bounds on LHS and RHS
  have hpref_bin : 7.77 * 306 / (Real.sqrt 0.003 * 0.0016) <
      7.77 * 306 / ((547 / 10000) * 0.0016) := by
    refine div_lt_div_of_pos_left (by norm_num) (by norm_num) ?_
    nlinarith
  have hlog_4sqrt_nonneg : 0 ≤ Real.log (4 / Real.sqrt 0.003) := by
    apply Real.log_nonneg
    have hsqrt_lt1 : Real.sqrt 0.003 < 1 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rw [one_le_div hsqrt_pos]
    linarith
  have hlog_bin2_nonneg :
      0 ≤ Real.log (Real.log ((306 : ℝ) / 0.0016) / Real.log (Real.sqrt 2) / 0.05) := by
    apply Real.log_nonneg
    have hlgt1 : 1 < Real.log ((306 : ℝ) / 0.0016) := by
      have hgt3 : (3 : ℝ) < (306 : ℝ) / 0.0016 := by norm_num
      have h1 := Real.log_lt_log (by norm_num) hgt3
      linarith
    rw [log_sqrt_two]
    have hls2 : Real.log 2 / 2 < 0.5 := by linarith
    have hls2_pos : 0 < Real.log 2 / 2 := by linarith
    have hq1 : 1 ≤ Real.log ((306 : ℝ) / 0.0016) / (Real.log 2 / 2) := by
      rw [one_le_div hls2_pos]
      linarith
    rw [le_div_iff₀ (by norm_num)]
    linarith
  have hprod_bin :
      Real.log (4 / Real.sqrt 0.003) *
          Real.log (Real.log ((306 : ℝ) / 0.0016) / Real.log (Real.sqrt 2) / 0.05) ≤
        4.32 * 6.58 :=
    mul_le_mul hlog_4sqrt_lt.le hlog_bin2_lt.le hlog_bin2_nonneg (by norm_num)
  have hlhs_bound :
      7.77 * 306 / (Real.sqrt 0.003 * 0.0016) * Real.log (4 / Real.sqrt 0.003) *
          Real.log (Real.log ((306 : ℝ) / 0.0016) / Real.log (Real.sqrt 2) / 0.05) ≤
        (7.77 * 306 / ((547 / 10000) * 0.0016)) * (4.32 * 6.58) := by
    rw [mul_assoc]
    exact mul_le_mul hpref_bin.le hprod_bin
      (mul_nonneg hlog_4sqrt_nonneg hlog_bin2_nonneg) (by norm_num)
  have hrhs_bound :
      (306 * 3.688 / (2 * 0.003 * 0.0016)) * 10.08 ≤
        306 * Real.log ((2 : ℝ) / 0.05) / (2 * 0.003 * 0.0016) *
          Real.log (Real.log ((2 : ℝ) / 0.05) / (0.003 * 0.05)) := by
    refine mul_le_mul ?_ hlog_dir2_gt.le (by norm_num) ?_
    · refine div_le_div_of_nonneg_right ?_ (by norm_num)
      linarith
    · positivity
  have hmid :
      ((7.77 : ℝ) * 306 / ((547 / 10000) * 0.0016)) * (4.32 * 6.58) ≤
        ((306 : ℝ) * 3.688 / (2 * 0.003 * 0.0016)) * 10.08 := by
    norm_num
  exact hlhs_bound.trans (hmid.trans hrhs_bound)

end Qatlib.Papers.RapidState24.MainResults.SamplingFiltering
