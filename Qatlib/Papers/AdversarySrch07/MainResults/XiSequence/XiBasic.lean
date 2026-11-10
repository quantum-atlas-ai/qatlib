/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdversarySrch07.MainResults.Definitions
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators ENNReal

namespace Qatlib.Papers.AdversarySrch07.MainResults.XiSequence

open Qatlib.Papers.AdversarySrch07.MainResults

@[simp]
theorem xi_zero : xi 0 = 1 := by
  simp [xi]

theorem xi_pos (i : ℕ) : 0 < xi i := by
  unfold xi
  exact div_pos (by exact_mod_cast Nat.centralBinom_pos i) (by positivity)

theorem xi_succ_mul (n : ℕ) :
    2 * ((n : ℝ) + 1) * xi (n + 1) = (2 * (n : ℝ) + 1) * xi n := by
  unfold xi
  have hR : ((n : ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ) =
      2 * (2 * (n : ℝ) + 1) * (Nat.centralBinom n : ℝ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ n
  have h4 : (4 : ℝ) ^ (n + 1) = 4 * 4 ^ n := by rw [pow_succ]; ring
  rw [h4]
  have h4n : (4 : ℝ) ^ n ≠ 0 := by positivity
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  linarith [hR]

theorem xi_succ_ratio (n : ℕ) :
    xi (n + 1) = xi n * ((n : ℝ) + 1 / 2) / ((n : ℝ) + 1) := by
  have h := xi_succ_mul n
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  have key : xi (n + 1) * (2 * ((n : ℝ) + 1)) = xi n * (2 * (n : ℝ) + 1) := by
    linarith [h]
  field_simp

  linarith [key]

theorem xi_antitone (n : ℕ) : xi (n + 1) ≤ xi n := by
  rw [xi_succ_ratio n]
  have hpos := xi_pos n
  have hratio : ((n : ℝ) + 1 / 2) / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  calc xi n * ((n : ℝ) + 1 / 2) / ((n : ℝ) + 1)
      = xi n * (((n : ℝ) + 1 / 2) / ((n : ℝ) + 1)) := by ring
    _ ≤ xi n * 1 := by
        exact mul_le_mul_of_nonneg_left hratio (le_of_lt hpos)
    _ = xi n := mul_one _

theorem xi_le_one (i : ℕ) : xi i ≤ 1 := by
  induction i with
  | zero => simp
  | succ n ih => exact (xi_antitone n).trans ih

theorem xi_mem_unit (i : ℕ) : xi i ∈ Set.Ioc (0 : ℝ) 1 :=
  ⟨xi_pos i, xi_le_one i⟩

end Qatlib.Papers.AdversarySrch07.MainResults.XiSequence
