/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OrderedInsert99.MainResults.Exact

/-!
# Excluding two-query insertion at large sizes

Specializes the invariant success bound to exclude exact two-query invariant insertion
algorithms when `6 ^ 8 ≤ N`. The module develops a large-size obstruction in the
ordered-insertion setting of [FarhiEtAl1999].

## Main statements

* `two_query_no_large`: rules out exact two-query invariant algorithms under the explicit size
  threshold.

## References

* [Farhi et al., 1999][FarhiEtAl1999]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.OrderedInsert99.MainResults

/-- For `N ≥ 6 ^ 8`, no exact two-query invariant insertion algorithm exists [FarhiEtAl1999]. -/
theorem two_query_no_large (N : ℕ) (hN : 6 ^ 8 ≤ N) :
    ¬ ExactInvariantAlgorithm N 2 := by
  rintro ⟨α, hα⟩
  have hNpos : 0 < N := by norm_num at hN ⊢; omega
  have hprob := exactStage_prob N 2 hNpos α hα
  have hb := invariant_success_bound N 2 hNpos α
  rw [hprob] at hb
  have hNle : (N : ℝ) ≤ (sinSum N) ^ 4 := by
    have hm := mul_le_mul_of_nonneg_right hb (by positivity : (0 : ℝ) ≤ (N : ℝ))
    have hcancel : (1 / (N : ℝ) * (sinSum N) ^ (2 * 2)) * (N : ℝ) = (sinSum N) ^ 4 := by
      field_simp
    linarith
  have hSle := sinSum_le_log N (by omega)
  have hSnn := sinSum_nonneg N hNpos
  set w : ℝ := Real.sqrt (Real.sqrt (N : ℝ)) with hwdef
  have hwpos : 0 < w := by
    rw [hwdef]; exact Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by positivity))
  have hw4 : w ^ 4 = (N : ℝ) := by
    rw [hwdef,
      show (Real.sqrt (Real.sqrt (N : ℝ))) ^ 4 = ((Real.sqrt (Real.sqrt (N : ℝ))) ^ 2) ^ 2 by ring,
      Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (N : ℝ))]
  have hw36 : 36 ≤ w := by
    have h1 : ((6 : ℝ) ^ 8) ≤ (N : ℝ) := by exact_mod_cast hN
    have h2 : Real.sqrt (Real.sqrt ((6 : ℝ) ^ 8)) = 36 := by
      rw [show ((6 : ℝ) ^ 8) = (((6 : ℝ) ^ 4) ^ 2) by ring, Real.sqrt_sq (by positivity)]
      rw [show ((6 : ℝ) ^ 4) = ((36 : ℝ) ^ 2) by norm_num, Real.sqrt_sq (by norm_num)]
    have h3 : Real.sqrt (Real.sqrt ((6 : ℝ) ^ 8)) ≤ Real.sqrt (Real.sqrt (N : ℝ)) :=
      Real.sqrt_le_sqrt (Real.sqrt_le_sqrt h1)
    rw [h2] at h3
    exact h3
  have hlogN : Real.log (N : ℝ) = 4 * Real.log w := by
    rw [← hw4, Real.log_pow]; push_cast; ring
  have hlogw : Real.log w ≤ 2 * Real.sqrt w := by
    have h1 : Real.log w = 2 * Real.log (Real.sqrt w) := by
      conv_lhs => rw [← Real.sq_sqrt hwpos.le]
      rw [Real.log_pow]; push_cast; ring
    have h2 : Real.log (Real.sqrt w) ≤ Real.sqrt w - 1 :=
      Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hwpos)
    have h3 : (0 : ℝ) ≤ Real.sqrt w := Real.sqrt_nonneg _
    rw [h1]; linarith
  set u : ℝ := Real.sqrt w with hudef
  have hu6 : 6 ≤ u := by
    rw [hudef]
    have h := Real.sqrt_le_sqrt hw36
    rwa [show Real.sqrt (36 : ℝ) = 6 by
      rw [show (36 : ℝ) = (6 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
  have hw_uu : w = u * u := by
    rw [hudef]
    rw [show Real.sqrt w * Real.sqrt w = Real.sqrt w ^ 2 by ring, Real.sq_sqrt hwpos.le]
  have hSlt : sinSum N < w := by
    have hlogbound : Real.log (N : ℝ) ≤ 8 * u := by
      rw [hlogN, hudef]
      linarith [hlogw]
    have hSb : sinSum N ≤ (16 / Real.pi) * u + 4 := by
      have hm := mul_le_mul_of_nonneg_left hlogbound (by positivity : (0 : ℝ) ≤ 2 / Real.pi)
      have he : (2 / Real.pi) * (8 * u) = (16 / Real.pi) * u := by ring
      linarith
    have hupi : (16 : ℝ) / Real.pi < (16 : ℝ) / 3 := by
      rw [div_lt_div_iff₀ Real.pi_pos (by norm_num)]
      nlinarith [Real.pi_gt_three]
    have h16 : (16 / Real.pi) * u < (16 / 3) * u :=
      mul_lt_mul_of_pos_right hupi (by linarith : (0 : ℝ) < u)
    have hquad : (16 / 3) * u + 4 ≤ u * u := by
      have h1 : (0 : ℝ) ≤ u - 6 := by linarith
      have h2 : (0 : ℝ) ≤ u + 2 / 3 := by linarith
      have hmul := mul_nonneg h1 h2
      nlinarith
    rw [hw_uu]
    linarith
  have hpow : (sinSum N) ^ 4 < w ^ 4 :=
    pow_lt_pow_left₀ hSlt hSnn (by norm_num : (4 : ℕ) ≠ 0)
  rw [hw4] at hpow
  linarith

end Qatlib.Papers.OrderedInsert99.MainResults
