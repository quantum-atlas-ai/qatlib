/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Sine coefficients and the path correlation bound

The sine coefficients `scoef` satisfy the endpoint and recurrence relations for a finite path.
An algebraic sum-of-squares identity yields `path_shift_le`, bounding adjacent correlation by
`cos (theta m)` times the squared norm. The phase-estimation setting is described in
[VanDamEtAl2007].

## Main statements

* `sos_abstract`: For `m ≥ 2`, nonvanishing interior coefficients satisfying the stated
  recurrence and endpoint relations express the path quadratic-form difference as the given
  weighted sum of squares.
* `path_shift_le`: For positive `m`, the adjacent correlation of any real sequence over `m`
  coordinates is at most `cos (theta m)` times its squared norm over those coordinates.

## References

* [van Dam et al., 2007][VanDamEtAl2007]
-/

noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.PhaseEst07.MainResults.Shared

/-- The angle `π / (m + 1)` associated with a path of length `m`. -/
def theta (m : ℕ) : ℝ := Real.pi / ((m : ℝ) + 1)

/-- The sine coefficient `sin ((k + 1) * theta m)`. -/
def scoef (m : ℕ) (k : ℕ) : ℝ := Real.sin (((k : ℝ) + 1) * theta m)

/-- The path angle `theta m` is positive. -/
lemma theta_pos (m : ℕ) : 0 < theta m := by
  unfold theta
  have h : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  exact div_pos Real.pi_pos h

/-- Multiplying `theta m` by `m + 1` gives `π`. -/
lemma theta_mul (m : ℕ) : ((m : ℝ) + 1) * theta m = Real.pi := by
  unfold theta
  have h : ((m : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-- The sine coefficient at index `m` vanishes. -/
lemma scoef_self (m : ℕ) : scoef m m = 0 := by
  unfold scoef
  rw [theta_mul, Real.sin_pi]

/-- The sine coefficient is nonnegative for indices at most `m`. -/
lemma scoef_nonneg {m j : ℕ} (h : j ≤ m) : 0 ≤ scoef m j := by
  unfold scoef
  apply Real.sin_nonneg_of_nonneg_of_le_pi
  · have hth := theta_pos m
    have : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
    exact mul_nonneg this hth.le
  · have hjm : (j : ℝ) + 1 ≤ (m : ℝ) + 1 := by
      have : (j : ℝ) ≤ m := by exact_mod_cast h
      linarith
    have hth := theta_pos m
    calc ((j : ℝ) + 1) * theta m ≤ ((m : ℝ) + 1) * theta m := by
          exact mul_le_mul_of_nonneg_right hjm hth.le
      _ = Real.pi := theta_mul m

/-- The sine coefficient is positive for indices strictly less than `m`. -/
lemma scoef_pos {m k : ℕ} (hk : k < m) : 0 < scoef m k := by
  unfold scoef
  apply Real.sin_pos_of_pos_of_lt_pi
  · have hth := theta_pos m
    have : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    exact mul_pos this hth
  · have hkm : (k : ℝ) + 1 < (m : ℝ) + 1 := by
      have : (k : ℝ) < m := by exact_mod_cast hk
      linarith
    have hth := theta_pos m
    have hlt : ((k : ℝ) + 1) * theta m < ((m : ℝ) + 1) * theta m :=
      mul_lt_mul_of_pos_right hkm hth
    rwa [theta_mul m] at hlt

/-- The sine coefficients satisfy the second-order recurrence with coefficient `2 * cos (theta
m)`. -/
lemma scoef_rec (m k : ℕ) :
    scoef m (k + 1 + 1) + scoef m k = 2 * Real.cos (theta m) * scoef m (k + 1) := by
  unfold scoef
  have h1 : (((k : ℝ) + 1 + 1) + 1) * theta m = (((k : ℝ) + 1) + 1) * theta m + theta m := by
    ring
  have h2 : (((k : ℝ) + 1)) * theta m = (((k : ℝ) + 1) + 1) * theta m - theta m := by
    ring
  push_cast
  rw [show ((k : ℝ) + 1 + 1 + 1) * theta m = ((k : ℝ) + 1 + 1) * theta m + theta m by ring]
  rw [show ((k : ℝ) + 1) * theta m = ((k : ℝ) + 1 + 1) * theta m - theta m by ring]
  rw [Real.sin_add, Real.sin_sub]
  ring

/-- The coefficient at index one is `2 * cos (theta m)` times the coefficient at index zero. -/
lemma scoef_one (m : ℕ) : scoef m 1 = 2 * Real.cos (theta m) * scoef m 0 := by
  unfold scoef
  push_cast
  simp only [one_add_one_eq_two, zero_add, one_mul]
  rw [Real.sin_two_mul]
  ring

/-- For `m ≥ 2`, nonvanishing interior coefficients satisfying the stated recurrence and
endpoint relations express the path quadratic-form difference as the given weighted sum of
squares. -/
lemma sos_abstract (m : ℕ) (hm : 2 ≤ m) (c : ℝ) (a : ℕ → ℝ) (p : ℕ → ℝ)
    (ha : ∀ k, k < m → a k ≠ 0)
    (h1 : a 1 = c * a 0)
    (hrec : ∀ k, a (k + 1 + 1) + a k = c * a (k + 1))
    (hm0 : a m = 0) :
    c * (∑ i ∈ Finset.range m, (p i) ^ 2) - 2 * (∑ t ∈ Finset.range (m - 1), p t * p (t + 1))
      = ∑ k ∈ Finset.range m,
          (a (k + 1) / a k) * (p k - (a k / a (k + 1)) * p (k + 1)) ^ 2 := by

  have hlast : (a ((m - 1) + 1) / a (m - 1)) *
      (p (m - 1) - (a (m - 1) / a ((m - 1) + 1)) * p ((m - 1) + 1)) ^ 2 = 0 := by
    have hm' : (m - 1) + 1 = m := by omega
    rw [hm', hm0]
    simp

  conv_rhs =>
    rw [show m = (m - 1) + 1 by omega]
    rw [Finset.sum_range_succ]
    rw [hlast, add_zero]

  have hterm : ∀ k ∈ Finset.range (m - 1),
      (a (k + 1) / a k) * (p k - (a k / a (k + 1)) * p (k + 1)) ^ 2
        = (a (k + 1) / a k) * (p k) ^ 2 + (a k / a (k + 1)) * (p (k + 1)) ^ 2
          - 2 * (p k * p (k + 1)) := by
    intro k hk
    have hk' : k < m - 1 := Finset.mem_range.mp hk
    have hkm : k < m := by omega
    have hk1 : k + 1 < m := by omega
    have hA : a k ≠ 0 := ha k hkm
    have hB : a (k + 1) ≠ 0 := ha (k + 1) hk1
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum]

  have hS1 := Finset.sum_range_succ' (fun k => (a (k + 1) / a k) * (p k) ^ 2) (m - 2)
  rw [show m - 2 + 1 = m - 1 by omega] at hS1
  have hS2 := Finset.sum_range_succ
    (fun k => (a k / a (k + 1)) * (p (k + 1)) ^ 2) (m - 2)
  rw [show m - 2 + 1 = m - 1 by omega] at hS2

  have hmid : (∑ k ∈ Finset.range (m - 2), (a (k + 1 + 1) / a (k + 1)) * (p (k + 1)) ^ 2)
      + (∑ k ∈ Finset.range (m - 2), (a k / a (k + 1)) * (p (k + 1)) ^ 2)
      = ∑ k ∈ Finset.range (m - 2), c * (p (k + 1)) ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hk2 : k < m - 2 := Finset.mem_range.mp hk
    have hk1m : k + 1 < m := by omega
    have hA : a (k + 1) ≠ 0 := ha (k + 1) hk1m
    have hcoef : a (k + 1 + 1) / a (k + 1) + a k / a (k + 1) = c := by
      field_simp
      linarith [hrec k]
    rw [← add_mul, hcoef]

  have hb0 : a 1 / a 0 = c := by
    have h0 : a 0 ≠ 0 := ha 0 (by omega)
    rw [h1]
    field_simp
  have hbm : a (m - 2) / a (m - 1) = c := by
    have h0 : a (m - 1) ≠ 0 := ha (m - 1) (by omega)
    have hr := hrec (m - 2)
    rw [show m - 2 + 1 + 1 = m by omega, show m - 2 + 1 = m - 1 by omega, hm0,
      zero_add] at hr
    rw [hr]
    field_simp

  have hX : (∑ i ∈ Finset.range m, (p i) ^ 2)
      = (p 0) ^ 2 + (∑ k ∈ Finset.range (m - 2), (p (k + 1)) ^ 2) + (p (m - 1)) ^ 2 := by
    have hs1 := Finset.sum_range_succ (fun i => (p i) ^ 2) (m - 1)
    rw [show m - 1 + 1 = m by omega] at hs1
    have hs2 := Finset.sum_range_succ' (fun i => (p i) ^ 2) (m - 2)
    rw [show m - 2 + 1 = m - 1 by omega] at hs2
    rw [hs1, hs2]
    ring
  rw [hS1, hS2, hb0, hbm, hX]
  have hmid' : c * (∑ k ∈ Finset.range (m - 2), (p (k + 1)) ^ 2) =
      (∑ k ∈ Finset.range (m - 2), (a (k + 1 + 1) / a (k + 1)) * (p (k + 1)) ^ 2)
      + (∑ k ∈ Finset.range (m - 2), (a k / a (k + 1)) * (p (k + 1)) ^ 2) := by
    rw [Finset.mul_sum]
    exact hmid.symm
  have hkey : c * (p 0 ^ 2 + (∑ k ∈ Finset.range (m - 2), (p (k + 1)) ^ 2) +
      (p (m - 1)) ^ 2)
      = c * (p 0) ^ 2
        + ((∑ k ∈ Finset.range (m - 2), (a (k + 1 + 1) / a (k + 1)) * (p (k + 1)) ^ 2)
          + (∑ k ∈ Finset.range (m - 2), (a k / a (k + 1)) * (p (k + 1)) ^ 2))
        + c * (p (m - 1)) ^ 2 := by
    rw [mul_add, mul_add, hmid']
  rw [hkey]
  ring

/-- For positive `m`, the adjacent correlation of any real sequence over `m` coordinates is at
most `cos (theta m)` times its squared norm over those coordinates. -/
theorem path_shift_le (m : ℕ) (hm : 0 < m) (p : ℕ → ℝ) :
    ∑ t ∈ Finset.range (m - 1), p t * p (t + 1)
      ≤ Real.cos (theta m) * ∑ i ∈ Finset.range m, (p i) ^ 2 := by
  rcases m with _ | _ | m
  · omega
  · have hcos : Real.cos (theta 1) = 0 := by
      unfold theta
      norm_num
    simp [hcos]
  · have hm2 : 2 ≤ m + 2 := by omega
    have hid := sos_abstract (m + 2) hm2 (2 * Real.cos (theta (m + 2)))
      (scoef (m + 2)) p
      (fun k hk => (scoef_pos hk).ne')
      (scoef_one (m + 2))
      (fun k => scoef_rec (m + 2) k)
      (scoef_self (m + 2))
    have hE : 0 ≤ ∑ k ∈ Finset.range (m + 2),
        (scoef (m + 2) (k + 1) / scoef (m + 2) k) *
          (p k - (scoef (m + 2) k / scoef (m + 2) (k + 1)) * p (k + 1)) ^ 2 := by
      apply Finset.sum_nonneg
      intro k hk
      have hklt : k < m + 2 := Finset.mem_range.mp hk
      have hk1 : k + 1 ≤ m + 2 := by omega
      exact mul_nonneg (div_nonneg (scoef_nonneg hk1) (scoef_nonneg hklt.le))
        (sq_nonneg _)
    have hineq : 2 * (∑ t ∈ Finset.range (m + 2 - 1), p t * p (t + 1))
        ≤ 2 * Real.cos (theta (m + 2)) * ∑ i ∈ Finset.range (m + 2), (p i) ^ 2 := by
      linarith [hid, hE]
    have hmain : (∑ t ∈ Finset.range (m + 2 - 1), p t * p (t + 1))
        ≤ Real.cos (theta (m + 2)) * ∑ i ∈ Finset.range (m + 2), (p i) ^ 2 := by
      linarith [hineq]
    have harith : m + 2 - 1 = m + 1 := by omega
    have harg : ((m : ℝ) + 2 + 1) = ((m : ℝ) + 1 + 1 + 1) := by ring
    simpa [theta, harith, harg] using hmain

end Qatlib.Papers.PhaseEst07.MainResults.Shared
