/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPCAAssume18.ClassCentroid.ActualSampler
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Explicit budgets for centroid estimation

This module chooses the sample count and odd-median parameter for the classical nearest-centroid
estimator of [Tang2021]. With `Z = averageNormSq u V`, each mean uses `ceil(256 * Z^2 / eps^2) +
1` samples, while a base-four ceiling logarithm determines the median parameter from `delta`.

## Main statements

* `centroidSamples_budget` and `centroidSamples_upper` give the required variance budget and an
  explicit sample-count bound.
- `centroid_median_tail_formula` simplifies the median tail to `4^(-(r + 1))`.
* `centroidRounds_failure` and `centroid_chosen_failure` bound the chosen estimator's failure
  mass by `delta`.

## References

* [Tang, 2021][Tang2021], *Quantum principal component analysis only achieves an exponential
  speedup because of its state preparation assumptions*, Theorem 4 and Algorithm 4.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.QPCAAssume18.ClassCentroid

open Qatlib.Concepts.SqEstimation.InnerProduct

/-- Chooses `ceil(256 * Z^2 / eps^2) + 1` samples for each centroid mean. -/
def centroidSamples (Z eps : ℝ) : ℕ := ⌈256 * Z ^ 2 / eps ^ 2⌉₊ + 1

/-- Chooses the median parameter as the base-four ceiling logarithm of the natural ceiling of `1
/ delta`; the estimator uses `2 * centroidRounds delta + 1` means. -/
def centroidRounds (delta : ℝ) : ℕ := Nat.clog 4 ⌈1 / delta⌉₊

/-- For positive `eps`, the chosen sample count is positive and satisfies `256 * Z^2 ≤
centroidSamples Z eps * eps^2`. -/
theorem centroidSamples_budget (Z eps : ℝ) (heps : 0 < eps) :
    0 < centroidSamples Z eps ∧ 256 * Z ^ 2 ≤ (centroidSamples Z eps : ℝ) * eps ^ 2 := by
  refine ⟨by unfold centroidSamples; omega, ?_⟩
  have hceil := Nat.le_ceil (256 * Z ^ 2 / eps ^ 2)
  have hm : 256 * Z ^ 2 / eps ^ 2 ≤ (centroidSamples Z eps : ℝ) := by
    unfold centroidSamples
    push_cast
    linarith
  exact (div_le_iff₀ (sq_pos_of_pos heps)).mp hm

/-- The chosen sample count is strictly less than `256 * Z^2 / eps^2 + 2`. -/
theorem centroidSamples_upper (Z eps : ℝ) :
    (centroidSamples Z eps : ℝ) < 256 * Z ^ 2 / eps ^ 2 + 2 := by
  have hceil := Nat.ceil_lt_add_one (by positivity : 0 ≤ 256 * Z ^ 2 / eps ^ 2)
  unfold centroidSamples
  push_cast
  linarith

/-- Simplifies the explicit componentwise-median tail expression to `(1 / 4)^(r + 1)`. -/
theorem centroid_median_tail_formula (r : ℕ) :
    2 * (2 : ℝ) ^ (2 * r + 1) * (1 / 16 : ℝ) ^ (r + 1) =
      (1 / 4 : ℝ) ^ (r + 1) := by
  induction r with
  | zero => norm_num
  | succ r ih =>
    have hindex : 2 * (r + 1) + 1 = (2 * r + 1) + 2 := by omega
    calc
      _ = (2 * (2 : ℝ) ^ (2 * r + 1) * (1 / 16 : ℝ) ^ (r + 1)) * (1 / 4) := by
        rw [hindex, pow_add, pow_succ]
        norm_num
        ring
      _ = (1 / 4 : ℝ) ^ (r + 1 + 1) := by rw [ih]; simp only [pow_succ]

/-- For positive `delta`, the median tail expression at the chosen parameter is at most `delta`. -/
theorem centroidRounds_failure (delta : ℝ) (hdelta : 0 < delta) :
    2 * (2 : ℝ) ^ (2 * centroidRounds delta + 1) *
      (1 / 16 : ℝ) ^ (centroidRounds delta + 1) ≤ delta := by
  have hceil : 1 / delta ≤ (⌈1 / delta⌉₊ : ℝ) := Nat.le_ceil _
  have hpow : (⌈1 / delta⌉₊ : ℝ) ≤ (4 : ℝ) ^ centroidRounds delta := by
    exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 4) ⌈1 / delta⌉₊
  have hnext : (4 : ℝ) ^ centroidRounds delta ≤ (4 : ℝ) ^ (centroidRounds delta + 1) :=
    pow_le_pow_right₀ (by norm_num) (Nat.le_succ _)
  have hbudget : 1 ≤ delta * (4 : ℝ) ^ (centroidRounds delta + 1) := by
    have h := (div_le_iff₀ hdelta).mp (hceil.trans (hpow.trans hnext))
    nlinarith
  rw [centroid_median_tail_formula, one_div_pow]
  exact (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 4) _)).mpr hbudget

/-- For positive `n`, a unit anchor, and positive `eps` and `delta`, the centroid tensor
estimator with the chosen budgets has bad mass at most `delta`. This supplies explicit
budgets for the classical nearest-centroid estimate in [Tang2021]. -/
theorem centroid_chosen_failure {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (hn : 0 < n) (ha : vectorEnergy anchor = 1)
    (eps delta : ℝ) (heps : 0 < eps) (hdelta : 0 < delta) :
    sqBadMass (centroidTensorInput anchor u V hn ha) (generalTensorB anchor u V)
      (centroidSamples (averageNormSq u V) eps) (centroidRounds delta) eps ≤ delta := by
  exact (centroid_actual_median_guarantee anchor u V hn ha _ _ eps
    (centroidSamples_budget _ _ heps).1 heps (centroidSamples_budget _ _ heps).2).trans
      (centroidRounds_failure delta hdelta)

end Qatlib.Papers.QPCAAssume18.ClassCentroid
