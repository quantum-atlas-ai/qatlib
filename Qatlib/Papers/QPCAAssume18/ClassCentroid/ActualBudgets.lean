/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPCAAssume18.ClassCentroid.ActualSampler
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Floor.Ring
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.QPCAAssume18.ClassCentroid

open Qatlib.Concepts.SqEstimation.InnerProduct

def centroidSamples (Z eps : ℝ) : ℕ := ⌈256 * Z ^ 2 / eps ^ 2⌉₊ + 1

def centroidRounds (delta : ℝ) : ℕ := Nat.clog 4 ⌈1 / delta⌉₊

theorem centroidSamples_budget (Z eps : ℝ) (heps : 0 < eps) :
    0 < centroidSamples Z eps ∧ 256 * Z ^ 2 ≤ (centroidSamples Z eps : ℝ) * eps ^ 2 := by
  refine ⟨by unfold centroidSamples; omega, ?_⟩
  have hceil := Nat.le_ceil (256 * Z ^ 2 / eps ^ 2)
  have hm : 256 * Z ^ 2 / eps ^ 2 ≤ (centroidSamples Z eps : ℝ) := by
    unfold centroidSamples
    push_cast
    linarith
  exact (div_le_iff₀ (sq_pos_of_pos heps)).mp hm

theorem centroidSamples_upper (Z eps : ℝ) :
    (centroidSamples Z eps : ℝ) < 256 * Z ^ 2 / eps ^ 2 + 2 := by
  have hceil := Nat.ceil_lt_add_one (by positivity : 0 ≤ 256 * Z ^ 2 / eps ^ 2)
  unfold centroidSamples
  push_cast
  linarith

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

theorem centroid_chosen_failure {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (hn : 0 < n) (ha : vectorEnergy anchor = 1)
    (eps delta : ℝ) (heps : 0 < eps) (hdelta : 0 < delta) :
    sqBadMass (centroidTensorInput anchor u V hn ha) (generalTensorB anchor u V)
      (centroidSamples (averageNormSq u V) eps) (centroidRounds delta) eps ≤ delta := by
  exact (centroid_actual_median_guarantee anchor u V hn ha _ _ eps
    (centroidSamples_budget _ _ heps).1 heps (centroidSamples_budget _ _ heps).2).trans
      (centroidRounds_failure delta hdelta)

end Qatlib.Papers.QPCAAssume18.ClassCentroid
