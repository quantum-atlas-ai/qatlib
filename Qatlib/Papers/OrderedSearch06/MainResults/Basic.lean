/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OrderedSearch06.SdpForm.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.OrderedSearch06.MainResults

def tableBaseN : ℕ → ℕ
  | 2 => 6
  | 3 => 56
  | 4 => 605
  | _ => 0

def tableInfeasibleN : ℕ → ℕ
  | 2 => 7
  | 3 => 57
  | 4 => 606
  | _ => 0

theorem tableBaseLtInfeasible (k : ℕ) (hk : k = 2 ∨ k = 3 ∨ k = 4) :
    tableBaseN k < tableInfeasibleN k := by
  rcases hk with rfl | rfl | rfl <;> decide

def recursiveQueryCount (k0 b N : ℕ) : ℕ := k0 * Nat.clog b N

def sortingQueryBound (N : ℝ) : ℝ := 4 * N * (Real.log N / Real.log 605)

theorem sortingQueryBound_logBaseChange (N : ℝ) (hN : 0 < N) :
    sortingQueryBound N =
      4 * N * (Real.log N / Real.log 2) / (Real.log 605 / Real.log 2) := by
  unfold sortingQueryBound
  have h2 : Real.log 2 ≠ 0 := by
    have : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    exact ne_of_gt this
  field_simp

def classicalLowerBound (N : ℝ) : ℝ := Real.log N / Real.log 2

def quantumLowerBound (N : ℝ) : ℝ := (Real.log N - 1) / Real.pi

theorem quantumLowerBound_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    quantumLowerBound x ≤ quantumLowerBound y := by
  have hl : Real.log x ≤ Real.log y := Real.log_le_log hx hxy
  unfold quantumLowerBound
  have hp : 0 < Real.pi := Real.pi_pos
  rw [div_le_div_iff_of_pos_right hp]
  linarith

theorem recursiveQueryCount_pow {k0 b m : ℕ} (hb : 1 < b) :
    recursiveQueryCount k0 b (b ^ m) = k0 * m := by
  unfold recursiveQueryCount
  rw [Nat.clog_pow b m hb]

theorem recursiveQueryCount_mono (k0 b : ℕ) : Monotone (recursiveQueryCount k0 b) := by
  intro x y hxy
  unfold recursiveQueryCount
  exact Nat.mul_le_mul_left k0 (Nat.clog_monotone b hxy)

theorem recursiveQueryCount_pow_605 (m : ℕ) :
    recursiveQueryCount 4 605 (605 ^ m) = 4 * m := by
  rw [recursiveQueryCount_pow (by norm_num : 1 < 605)]

def searchQueryBound (N : ℝ) : ℝ := (4 * Real.log N) / Real.log 605

def previousSearchBound (N : ℝ) : ℝ := (3 * Real.log N) / Real.log 52

theorem four_log_two_lt_log_605 : 4 * Real.log 2 < Real.log 605 := by
  have h := Real.log_lt_log (show (0 : ℝ) < 16 by norm_num) (show (16 : ℝ) < 605 by norm_num)
  have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    have hp := Real.log_pow (2 : ℝ) 4
    norm_num at hp
    exact hp
  rwa [h16] at h

theorem three_log_two_lt_log_52 : 3 * Real.log 2 < Real.log 52 := by
  have h := Real.log_lt_log (show (0 : ℝ) < 8 by norm_num) (show (8 : ℝ) < 52 by norm_num)
  have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    have hp := Real.log_pow (2 : ℝ) 3
    norm_num at hp
    exact hp
  rwa [h8] at h

theorem four_log_52_lt_three_log_605 : 4 * Real.log 52 < 3 * Real.log 605 := by
  have h := Real.log_lt_log (show (0 : ℝ) < (52 : ℝ) ^ 4 by positivity)
    (show (52 : ℝ) ^ 4 < (605 : ℝ) ^ 3 by norm_num)
  have h52 : Real.log ((52 : ℝ) ^ 4) = 4 * Real.log 52 := Real.log_pow 52 4
  have h605 : Real.log ((605 : ℝ) ^ 3) = 3 * Real.log 605 := Real.log_pow 605 3
  rwa [h52, h605] at h

theorem searchQueryBound_lt_classical {N : ℝ} (hN : 1 < N) :
    searchQueryBound N < classicalLowerBound N := by
  have hNpos : 0 < Real.log N := Real.log_pos hN
  have h605 : 0 < Real.log 605 := Real.log_pos (by norm_num)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hkey : 4 * Real.log N * Real.log 2 < Real.log N * Real.log 605 := by
    have hm := mul_lt_mul_of_pos_left four_log_two_lt_log_605 hNpos
    nlinarith
  unfold searchQueryBound classicalLowerBound
  rw [div_lt_div_iff₀ h605 h2]
  exact hkey

theorem searchQueryBound_lt_previous {N : ℝ} (hN : 1 < N) :
    searchQueryBound N < previousSearchBound N := by
  have hNpos : 0 < Real.log N := Real.log_pos hN
  have h605 : 0 < Real.log 605 := Real.log_pos (by norm_num)
  have h52 : 0 < Real.log 52 := Real.log_pos (by norm_num)
  have hkey : 4 * Real.log N * Real.log 52 < 3 * Real.log N * Real.log 605 := by
    have hm := mul_lt_mul_of_pos_left four_log_52_lt_three_log_605 hNpos
    nlinarith
  unfold searchQueryBound previousSearchBound
  rw [div_lt_div_iff₀ h605 h52]
  exact hkey

theorem previousSearchBound_lt_classical {N : ℝ} (hN : 1 < N) :
    previousSearchBound N < classicalLowerBound N := by
  have hNpos : 0 < Real.log N := Real.log_pos hN
  have h52 : 0 < Real.log 52 := Real.log_pos (by norm_num)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hkey : 3 * Real.log N * Real.log 2 < Real.log N * Real.log 52 := by
    have hm := mul_lt_mul_of_pos_left three_log_two_lt_log_52 hNpos
    nlinarith
  unfold previousSearchBound classicalLowerBound
  rw [div_lt_div_iff₀ h52 h2]
  exact hkey

theorem searchQueryBound_pow (m : ℕ) :
    searchQueryBound ((605 : ℝ) ^ m) = 4 * m := by
  unfold searchQueryBound
  rw [Real.log_pow]
  have h605 : Real.log (605 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hassoc : (4 : ℝ) * ((m : ℝ) * Real.log 605) = ((4 : ℝ) * m) * Real.log 605 := by
    ring
  rw [hassoc, mul_div_cancel_right₀ _ h605]

theorem sortingQueryBound_eq_mul_search (N : ℝ) :
    sortingQueryBound N = N * searchQueryBound N := by
  unfold sortingQueryBound searchQueryBound
  ring

theorem sortingQueryBound_lt_classicalSorting {N : ℝ} (hN : 1 < N) :
    sortingQueryBound N < N * classicalLowerBound N := by
  have hNpos : 0 < N := by linarith
  rw [sortingQueryBound_eq_mul_search]
  exact mul_lt_mul_of_pos_left (searchQueryBound_lt_classical hN) hNpos

end Qatlib.Papers.OrderedSearch06.MainResults
