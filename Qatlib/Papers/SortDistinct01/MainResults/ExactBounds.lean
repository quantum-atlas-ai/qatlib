/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SortDistinct01.MainResults.AdversaryMethod
public import Qatlib.Papers.SortDistinct01.MainResults.Recurrence

@[expose] public section

/-!
# Exact-query specializations and recurrence decrease

At zero terminal error, the harmonic-number bound in Theorems 2 and 3 gives the
stated logarithmic lower bounds. Lemma 12's recursive argument decreases by
the elementary logarithm inequality applied after rescaling the input by eight.
-/

set_option autoImplicit false

open Qatlib.Papers.SortDistinct01.MainResults.AdversaryMethod
open Qatlib.Papers.SortDistinct01.MainResults.Recurrence

namespace Qatlib.Papers.SortDistinct01.MainResults

/-- The harmonic term in the exact bounds dominates its logarithmic replacement. -/
private theorem log_sub_one_le_harmonic {N : ℕ} (hN : 1 ≤ N) :
    Real.log (N : ℝ) - 1 ≤ (harmonic N : ℝ) - 1 := by
  have hp : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog := Real.log_le_log hp (show (N : ℝ) ≤ (N : ℝ) + 1 by linarith)
  have hh := log_add_one_le_harmonic N
  push_cast at hh
  linarith

/-- Theorem 2's numerical sorting lower bound in the exact case. -/
theorem theorem2_exact_case {N T : ℕ} {W : ℕ → ℝ} (hN : 1 ≤ N)
    (hW0 : W 0 = (Nat.factorial N : ℝ) * ((N : ℝ) * (harmonic N : ℝ) - N))
    (hstep : ∀ j < T, |W j - W (j + 1)| ≤ 2 * Real.pi * (Nat.factorial N : ℝ))
    (hWT : W T ≤ 0) :
    ((N : ℝ) / (2 * Real.pi)) * (Real.log (N : ℝ) - 1) ≤ (T : ℝ) := by
  have h := theorem2_sorting_lower_bound (ε := 0) (by norm_num) (by norm_num)
    hW0 hstep (by simpa using hWT)
  exact (mul_le_mul_of_nonneg_left (log_sub_one_le_harmonic hN)
    (by positivity)).trans (by simpa using h)

/-- Theorem 3's numerical element-distinctness lower bound in the exact case. -/
theorem theorem3_exact_case {N T : ℕ} {W : ℕ → ℝ} (hN : 1 ≤ N)
    (hW0 : W 0 = (Nat.factorial N : ℝ) * ((N : ℝ) * (harmonic N : ℝ) - N))
    (hstep : ∀ j < T,
      |W j - W (j + 1)| ≤ 2 * Real.pi * (Nat.factorial N : ℝ) * Real.sqrt (N : ℝ))
    (hWT : W T ≤ 0) :
    (Real.sqrt (N : ℝ) / (2 * Real.pi)) * (Real.log (N : ℝ) - 1) ≤ (T : ℝ) := by
  have h := theorem3_element_distinctness_lower_bound (ε := 0) hN (by norm_num) (by norm_num)
    hW0 hstep (by simpa using hWT)
  exact (mul_le_mul_of_nonneg_left (log_sub_one_le_harmonic hN)
    (by positivity)).trans (by simpa using h)

/-- The recursive argument of Lemma 12 is smaller than its input in the recursive branch. -/
theorem nextSize_lt (N : ℕ) (hN : 9 ≤ N) : nextSize N < N := by
  have hN' : (9 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hlog2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (x := 2) (by norm_num)
    linarith
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hr := Real.log_le_sub_one_of_pos (show 0 < (N : ℝ) / 8 by positivity)
  rw [Real.log_div hNp.ne' (by norm_num), hlog8] at hr
  have hlog : Real.logb 2 (N : ℝ) ≤ (N : ℝ) / 4 + 1 := by
    rw [Real.logb, div_le_iff₀ hlog2p]
    have hmul := mul_le_mul_of_nonneg_right hlog2
      (show 0 ≤ (N : ℝ) / 4 - 2 by linarith)
    linarith
  exact (Nat.floor_lt' (by omega)).2 (by linarith)

end Qatlib.Papers.SortDistinct01.MainResults
