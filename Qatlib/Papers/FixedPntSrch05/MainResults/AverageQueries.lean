/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.FixedPntSrch05.MainResults.AverageQueries

open Finset

def avgQueriesN (ε : ℝ) (n : ℕ) : ℝ :=
  (1 - ε) / 2
    + (1 + ε) / 2 * (1 - ε ^ 2) * (∑ j ∈ range n, ((j : ℝ) + 2) * (ε ^ 2) ^ j)
    + ((n : ℝ) + 1) * (1 + ε) / 2 * (ε ^ 2) ^ n

theorem avgQueriesN_eq (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) (n : ℕ) :
    avgQueriesN ε n = 1 + (1 - (ε ^ 2) ^ n) / (2 * (1 - ε)) := by
  have hden : (1 - ε) ≠ 0 := by
    intro h
    linarith
  induction n with
  | zero =>
      simp only [avgQueriesN, Finset.sum_range_zero, sum_empty, mul_zero, add_zero,
        Nat.cast_zero, zero_add, pow_zero, mul_one]
      field_simp
      ring
  | succ n ih =>
      have hd : avgQueriesN ε (n + 1) - avgQueriesN ε n = (1 + ε) / 2 * (ε ^ 2) ^ n := by
        simp only [avgQueriesN, Finset.sum_range_succ, pow_succ]
        push_cast
        ring
      have hr : (1 + (1 - (ε ^ 2) ^ (n + 1)) / (2 * (1 - ε)))
            - (1 + (1 - (ε ^ 2) ^ n) / (2 * (1 - ε))) = (1 + ε) / 2 * (ε ^ 2) ^ n := by
        rw [pow_succ]
        field_simp [hden]
        ring
      linarith [ih, hd, hr]

theorem average_queries_eq (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) (q : ℕ) (hq : 1 ≤ q) :
    (1 - ε) / 2
      + (1 + ε) / 2 * (1 - ε ^ 2) * (∑ k ∈ range (q - 1), ((k : ℝ) + 2) * (ε ^ 2) ^ k)
      + (q : ℝ) * (1 + ε) / 2 * ε ^ (2 * q - 2)
    = 1 + (1 - ε ^ (2 * q - 2)) / (2 * (1 - ε)) := by
  have h := avgQueriesN_eq ε hε0 hε1 (q - 1)
  unfold avgQueriesN at h
  have hq' : q - 1 + 1 = q := by omega
  have hcast : (((q - 1 : ℕ) : ℝ) + 1) = (q : ℝ) := by
    have hc := congrArg (fun n : ℕ => (n : ℝ)) hq'
    simpa [Nat.cast_add, Nat.cast_one] using hc
  have hx : (ε ^ 2) ^ (q - 1) = ε ^ (2 * q - 2) := by
    rw [← pow_mul]
    congr 1
    omega
  rw [hcast, hx] at h
  exact h

def clSum (ε : ℝ) (m : ℕ) : ℝ := ∑ k ∈ range m, ((k : ℝ) + 1) * ε ^ k

theorem clSum_eq (ε : ℝ) (hε : ε ≠ 1) (m : ℕ) :
    (1 - ε) * clSum ε m = (1 - ε ^ m) / (1 - ε) - (m : ℝ) * ε ^ m := by
  have hden : (1 : ℝ) - ε ≠ 0 := by
    intro h
    apply hε
    linarith
  induction m with
  | zero => simp [clSum]
  | succ m ih =>
      push_cast
      have hd : (1 - ε) * clSum ε (m + 1) - (1 - ε) * clSum ε m
          = (1 - ε) * ((m : ℝ) + 1) * ε ^ m := by
        simp only [clSum, Finset.sum_range_succ]
        push_cast
        ring
      have hr : ((1 - ε ^ (m + 1)) / (1 - ε) - ((m : ℝ) + 1) * ε ^ (m + 1))
            - ((1 - ε ^ m) / (1 - ε) - (m : ℝ) * ε ^ m)
          = (1 - ε) * ((m : ℝ) + 1) * ε ^ m := by
        rw [pow_succ]
        push_cast
        field_simp [hden]
        ring
      linarith [ih, hd, hr]

def classicalQueries (ε : ℝ) (q : ℕ) : ℝ :=
  (1 - ε) * clSum ε (2 * q) + ((2 * q : ℕ) : ℝ) * ε ^ (2 * q)

theorem classical_queries_eq (ε : ℝ) (hε : ε ≠ 1) (q : ℕ) :
    classicalQueries ε q = (1 - ε ^ (2 * q)) / (1 - ε) := by
  unfold classicalQueries
  rw [clSum_eq ε hε (2 * q)]
  ring

theorem two_average_gt_classical (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (q : ℕ) (hq : 1 ≤ q) :
    2 * (1 + (1 - ε ^ (2 * q - 2)) / (2 * (1 - ε))) > (1 - ε ^ (2 * q)) / (1 - ε) := by
  have hden : (1 : ℝ) - ε ≠ 0 := by
    intro h
    linarith
  rw [gt_iff_lt]
  have hp : ε ^ (2 * q) = ε ^ (2 * q - 2) * ε ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  have hkey :
      2 * (1 + (1 - ε ^ (2 * q - 2)) / (2 * (1 - ε))) - (1 - ε ^ (2 * q)) / (1 - ε)
        = 2 - ε ^ (2 * q - 2) * (1 + ε) := by
    rw [hp]
    field_simp [hden]
    ring
  have hpos : 0 < 2 - ε ^ (2 * q - 2) * (1 + ε) := by
    have hle1 : ε ^ (2 * q - 2) ≤ 1 := pow_le_one₀ hε0.le hε1.le
    have hstep : ε ^ (2 * q - 2) * (1 + ε) ≤ 1 * (1 + ε) :=
      mul_le_mul_of_nonneg_right hle1 (by linarith)
    linarith
  linarith [hkey, hpos]

end Qatlib.Papers.FixedPntSrch05.MainResults.AverageQueries
