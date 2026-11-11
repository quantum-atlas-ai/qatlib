/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.InvFreeSampling.BernoulliTail
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

/-!
# Bernoulli frequency estimates for rare outcomes

This module computes the expectation, variance, and mean-square sampling error of a Boolean
frequency estimator. `bernoulliRareShots` chooses a positive sample count from a bound on the
true-outcome probability; `bernoulli_rare_tail` and `bernoulli_rare_success` give the
corresponding deviation guarantees. For background, see [NielsenChuang2010].

## Main statements

* `bernoulli_frequency_mean_square`: For a positive sample size `n`, the mean squared error of
  the empirical true frequency under independent samples is `p.prob true * (1 - p.prob true) /
  n`.
* `bernoulli_rare_tail`: If `kappa > 0` and the true probability is at most `delta²`, the
  empirical frequency with `bernoulliRareShots delta kappa` samples deviates by more than
  `kappa` with probability at most `1 / 160`.
* `bernoulli_rare_success`: If `kappa > 0` and the true probability is at most `delta²`, the
  empirical frequency with the prescribed sample count has absolute error at most `kappa` with
  probability at least `159 / 160`.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.AmplitudeCore.InvFreeSampling

set_option autoImplicit false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open scoped Classical BigOperators

/-- The positive sample count `max 1 (Nat.ceil (160 * delta² / kappa²))` for the rare-outcome
frequency estimate. -/
noncomputable def bernoulliRareShots (delta kappa : ℝ) : ℕ :=
  max 1 (Nat.ceil (160 * delta ^ 2 / kappa ^ 2))

/-- The empirical frequency of true values in a finite Boolean sample, expressed as the average
of the Boolean indicator. -/
noncomputable def bernoulliFrequency {n : ℕ} (omega : Fin n → Bool) : ℝ :=
  Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (fun b => if b then (1 : ℝ) else 0) omega

/-- The expectation of the true-value indicator is the probability of true. -/
theorem bernoulli_expect (p : FinDist Bool) :
    p.expect (fun b => if b then (1 : ℝ) else 0) = p.prob true := by
  simpa only [boolIndicator] using! expect_boolIndicator p

/-- The variance of the true-value indicator is `p.prob true * (1 - p.prob true)`. -/
theorem bernoulli_variance (p : FinDist Bool) :
    p.variance (fun b => if b then (1 : ℝ) else 0) =
      p.prob true * (1 - p.prob true) := by
  simpa only [expect_boolIndicator, boolIndicator] using! variance_boolIndicator p

/-- The variance of the true-value indicator is at most the probability of true. -/
theorem bernoulli_variance_le (p : FinDist Bool) :
    p.variance (fun b => if b then (1 : ℝ) else 0) ≤ p.prob true := by
  rw [bernoulli_variance]
  nlinarith [sq_nonneg (p.prob true)]

/-- For a positive sample size `n`, the mean squared error of the empirical true frequency under
independent samples is `p.prob true * (1 - p.prob true) / n`. -/
theorem bernoulli_frequency_mean_square {n : ℕ} (p : FinDist Bool) (hn : 0 < n) :
    (∑ omega : Fin n → Bool,
      p.probOf omega * (bernoulliFrequency omega - p.prob true) ^ 2) =
      p.prob true * (1 - p.prob true) / (n : ℝ) := by
  have h :=
      Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect_avg_sub_sq p
      (fun b => if b then (1 : ℝ) else 0) hn
  rw [bernoulli_expect, bernoulli_variance] at h
  exact h

/-- The rare-outcome sample count is strictly positive for all real parameters. -/
theorem bernoulli_rare_shots_pos (delta kappa : ℝ) :
    0 < bernoulliRareShots delta kappa := by
  exact lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) (Nat.le_max_left 1 _)

/-- A zero rare-probability parameter gives sample count one. -/
theorem bernoulli_rare_shots_zero (kappa : ℝ) :
    bernoulliRareShots 0 kappa = 1 := by
  simp [bernoulliRareShots]

/-- The chosen sample count is at least `160 * delta² / kappa²` after casting to the reals. -/
theorem bernoulli_rare_shots_lower (delta kappa : ℝ) :
    160 * delta ^ 2 / kappa ^ 2 ≤ (bernoulliRareShots delta kappa : ℝ) := by
  have hc : 160 * delta ^ 2 / kappa ^ 2 ≤
      (Nat.ceil (160 * delta ^ 2 / kappa ^ 2) : ℝ) := Nat.le_ceil _
  have hm : Nat.ceil (160 * delta ^ 2 / kappa ^ 2) ≤ bernoulliRareShots delta kappa :=
    Nat.le_max_right 1 _
  exact hc.trans (Nat.cast_le.mpr hm)

/-- The chosen sample count is at most `1 + 160 * delta² / kappa²` after casting to the reals. -/
theorem bernoulli_rare_shots_le (delta kappa : ℝ) :
    (bernoulliRareShots delta kappa : ℝ) ≤ 1 + 160 * delta ^ 2 / kappa ^ 2 := by
  have hx : 0 ≤ 160 * delta ^ 2 / kappa ^ 2 :=
    div_nonneg (mul_nonneg (by norm_num) (sq_nonneg delta)) (sq_nonneg kappa)
  have hc : (Nat.ceil (160 * delta ^ 2 / kappa ^ 2) : ℝ) ≤
      1 + 160 * delta ^ 2 / kappa ^ 2 := by
    have h := (Nat.ceil_lt_add_one hx).le
    linarith
  rcases le_total 1 (Nat.ceil (160 * delta ^ 2 / kappa ^ 2)) with h | h
  · rw [bernoulliRareShots, max_eq_right h]
    exact hc
  · rw [bernoulliRareShots, max_eq_left h, Nat.cast_one]
    linarith

/-- If `kappa > 0` and the true probability is at most `delta²`, the empirical frequency with
`bernoulliRareShots delta kappa` samples deviates by more than `kappa` with probability at
most `1 / 160`. -/
theorem bernoulli_rare_tail (p : FinDist Bool) (delta kappa : ℝ)
    (hk : 0 < kappa) (hp : p.prob true ≤ delta ^ 2) :
    p.probEvent (L := bernoulliRareShots delta kappa)
      (fun omega => kappa < |bernoulliFrequency omega - p.prob true|) ≤ 1 / 160 := by
  have hn := bernoulli_rare_shots_pos delta kappa
  have hnR : (0 : ℝ) < (bernoulliRareShots delta kappa : ℝ) := Nat.cast_pos.mpr hn
  have hk2 : 0 < kappa ^ 2 := pow_pos hk 2
  have hd : 0 < (bernoulliRareShots delta kappa : ℝ) * kappa ^ 2 := mul_pos hnR hk2
  have hsize : 160 * delta ^ 2 ≤ (bernoulliRareShots delta kappa : ℝ) * kappa ^ 2 :=
    (div_le_iff₀ hk2).mp (bernoulli_rare_shots_lower delta kappa)
  have hvar := (bernoulli_variance_le p).trans hp
  have hcheb :=
      Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.chebyshev_avg p
      (fun b => if b then (1 : ℝ) else 0) hn kappa hk
  rw [bernoulli_expect] at hcheb
  calc
    p.probEvent (L := bernoulliRareShots delta kappa)
        (fun omega => kappa < |bernoulliFrequency omega - p.prob true|)
      ≤ p.variance (fun b => if b then (1 : ℝ) else 0) /
          ((bernoulliRareShots delta kappa : ℝ) * kappa ^ 2) := hcheb
    _ ≤ delta ^ 2 / ((bernoulliRareShots delta kappa : ℝ) * kappa ^ 2) :=
      (div_le_div_iff_of_pos_right hd).mpr hvar
    _ ≤ 1 / 160 := by
      apply (div_le_iff₀ hd).mpr
      nlinarith [hsize]

/-- If `kappa > 0` and the true probability is at most `delta²`, the empirical frequency with
the prescribed sample count has absolute error at most `kappa` with probability at least
`159 / 160`. -/
theorem bernoulli_rare_success (p : FinDist Bool) (delta kappa : ℝ)
    (hk : 0 < kappa) (hp : p.prob true ≤ delta ^ 2) :
    159 / 160 ≤ p.probEvent (L := bernoulliRareShots delta kappa)
      (fun omega => |bernoulliFrequency omega - p.prob true| ≤ kappa) := by
  have hsplit :
      p.probEvent (L := bernoulliRareShots delta kappa)
          (fun omega => kappa < |bernoulliFrequency omega - p.prob true|) +
        p.probEvent (L := bernoulliRareShots delta kappa)
          (fun omega => |bernoulliFrequency omega - p.prob true| ≤ kappa) = 1 := by
    simpa only [not_lt] using
      (probEvent_compl (L := bernoulliRareShots delta kappa) p
        (fun omega => kappa < |bernoulliFrequency omega - p.prob true|))
  have htail := bernoulli_rare_tail p delta kappa hk hp
  linarith

end Qatlib.Concepts.AdversaryBounds.AdvDuality
