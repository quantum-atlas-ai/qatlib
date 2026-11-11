/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.WalkSpatial08.MainResults.SpectralBounds
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Logarithmic gap bounds and final overlap

This module bounds the weighted inverse-gap sum by the logarithm of the lattice size. It uses
this bound at the balanced control parameter to give an explicit positive lower bound for
`finalOverlapSq`.

The controlled spatial-search setting is described in [Tulsi2008].

## Main statements

* `sumInvGap_le_logLattice`: inverse-gap sum bounded by four times the lattice logarithm.
* `finalOverlapSq_ge`: balanced overlap square at least `1 / 33`.

## References

* [Tulsi, 2008][Tulsi2008]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.WalkSpatial08.MainResults

/-- The weighted inverse-gap sum is nonnegative for every lattice side length. -/
theorem sumInvGap_nonneg (n : ℕ) : 0 ≤ sumInvGap n := by
  unfold sumInvGap
  exact Finset.sum_nonneg fun p _ =>
    Finset.sum_nonneg fun q _ => term_nonneg n p q

/-- For positive `n`, the harmonic number at `n / 2 + 1` is at most `1 + log n`. -/
theorem harmonic_half_succ_le {n : ℕ} (hn : 1 ≤ n) :
    (harmonic (n / 2 + 1) : ℝ) ≤ 1 + Real.log (n : ℝ) := by
  have hbase : (harmonic (n / 2 + 1) : ℝ) ≤
      1 + Real.log ((n / 2 + 1 : ℕ) : ℝ) := harmonic_le_one_add_log (n / 2 + 1)
  have hle : ((n / 2 + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
    have h : n / 2 + 1 ≤ n := by omega
    exact_mod_cast h
  have hpos : (0 : ℝ) < ((n / 2 + 1 : ℕ) : ℝ) := by positivity
  have hlog : Real.log ((n / 2 + 1 : ℕ) : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hpos hle
  linarith

/-- For side length at least sixteen, the weighted inverse-gap sum is at most four times the
logarithm of the lattice size. See [Main result: O(sqrt(N log N)) two-dimensional spatial
search][Tulsi2008]. -/
theorem sumInvGap_le_logLattice {n : ℕ} (hn : 16 ≤ n) :
    sumInvGap n ≤ 4 * logLattice n := by
  have hn0 : 0 < n := by omega
  have hlog : 1 ≤ logLattice n := logLattice_ge_one_of_ge_16 hn
  have hsum : sumInvGap n ≤ 4 * (harmonic (n / 2 + 1) : ℝ) := sumInvGap_le n hn0
  have hH : (harmonic (n / 2 + 1) : ℝ) ≤ 1 + Real.log (n : ℝ) :=
    harmonic_half_succ_le (by omega)
  have htwo : logLattice n = 2 * Real.log (n : ℝ) := logLattice_eq_two_log hn0
  have hlogn : 1 ≤ Real.log (n : ℝ) := by
    have h16pos : (0 : ℝ) < 16 := by norm_num
    have hexp : Real.exp 1 ≤ (16 : ℝ) := by
      have h3 := Real.exp_one_lt_three
      linarith
    have hlog16 : 1 ≤ Real.log (16 : ℝ) := (Real.le_log_iff_exp_le h16pos).mpr hexp
    have hle : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact le_trans hlog16 (Real.log_le_log h16pos hle)
  calc sumInvGap n ≤ 4 * (harmonic (n / 2 + 1) : ℝ) := hsum
    _ ≤ 4 * (1 + Real.log (n : ℝ)) := by linarith
    _ ≤ 4 * logLattice n := by rw [htwo]; nlinarith

/-- The model overlap square `1 / (1 + 8 * cos δ² * sumInvGap n)`. -/
def finalOverlapSq (n : ℕ) (δ : ℝ) : ℝ :=
  1 / (1 + 8 * Real.cos δ ^ 2 * sumInvGap n)

/-- For side length at least sixteen, the overlap square at the balanced control parameter is at
least `1 / 33`. See [Main result: O(sqrt(N log N)) two-dimensional spatial
search][Tulsi2008]. -/
theorem finalOverlapSq_ge {n : ℕ} (hn : 16 ≤ n) :
    1 / 33 ≤ finalOverlapSq n (deltaStar n) := by
  have hlog : 1 ≤ logLattice n := logLattice_ge_one_of_ge_16 hn
  have hL := logLattice_pos hlog
  have hsum : sumInvGap n ≤ 4 * logLattice n := sumInvGap_le_logLattice hn
  have hcos : (Real.cos (deltaStar n)) ^ 2 = 1 / logLattice n := sq_cos_deltaStar hlog
  have hkey : 8 * Real.cos (deltaStar n) ^ 2 * sumInvGap n ≤ 32 := by
    rw [hcos]
    have h1 : (1 / logLattice n) * sumInvGap n ≤
        (1 / logLattice n) * (4 * logLattice n) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    have h8 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 8)
    have h2 : 8 * ((1 / logLattice n) * (4 * logLattice n)) = 32 := by
      field_simp
      norm_num
    rw [h2] at h8
    linarith [h8]
  have hden : 0 < 1 + 8 * Real.cos (deltaStar n) ^ 2 * sumInvGap n := by
    have hmul : 0 ≤ 8 * Real.cos (deltaStar n) ^ 2 * sumInvGap n :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sumInvGap_nonneg n)
    linarith
  have hle : 1 + 8 * Real.cos (deltaStar n) ^ 2 * sumInvGap n ≤ 33 := by linarith
  unfold finalOverlapSq
  exact one_div_le_one_div_of_le hden hle

end Qatlib.Papers.WalkSpatial08.MainResults
