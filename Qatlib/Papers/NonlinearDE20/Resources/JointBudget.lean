/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.NonlinearDE20.Resources.ScalarBudgets
public import Mathlib.Tactic

@[expose] public section

/-!
# Joint step and copy budget

The step budget and the copy-denominator budget of [LloydEtAl2020] are stated separately, each
with its own free parameter. This module chooses a single step count, derives the clock resolution
`t / T` from it, and then picks the number of copies large enough for the copy denominator budget
while exceeding `m * T`, which is the regime `n ≫ mT` used by the paper.

## Main statements

* `joint_copy_step_budget`: there are a positive step count `T` and a copy count `n` with
  `m * T < n` such that both the accumulated step error and the copy denominator ratio are at most
  the positive tolerance.

## References

* [Lloyd et al., 2020][LloydEtAl2020]
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.NonlinearDE20.Resources.Joint

open Qatlib.Papers.NonlinearDE20.Resources.Budgets

/-- For positive energy scale, time and tolerance there are a positive step count `T` and a copy
count `n > m * T` such that the accumulated step error and the copy denominator ratio are both at
most the tolerance [LloydEtAl2020]. -/
theorem joint_copy_step_budget (E2 t ε : ℝ) (m : ℕ)
    (hE2 : 0 < E2) (hε : 0 < ε) (ht : 0 < t) (hm : 1 ≤ m) :
    ∃ T n : ℕ, 0 < T ∧ m * T < n ∧
      E2 * (T : ℝ) * (t / (T : ℝ)) ^ 2 ≤ ε ∧
      E2 * t * (t / (T : ℝ)) * (m : ℝ) ^ 2 / (n : ℝ) ≤ ε := by
  have hpos : 0 < E2 * t ^ 2 / ε := by positivity
  let T : ℕ := Nat.ceil (E2 * t ^ 2 / ε)
  let c : ℕ := Nat.ceil (E2 * t * (t / (T : ℝ)) * (m : ℝ) ^ 2 / ε)
  let n : ℕ := max (m * T) c + 1
  have hTdef : T = Nat.ceil (E2 * t ^ 2 / ε) := rfl
  have hcdef : c = Nat.ceil (E2 * t * (t / (T : ℝ)) * (m : ℝ) ^ 2 / ε) := rfl
  have hndef : n = max (m * T) c + 1 := rfl
  have hTpos : 0 < T := by rw [hTdef]; exact Nat.ceil_pos.mpr hpos
  have hT0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hTpos
  have hTge : E2 * t ^ 2 / ε ≤ (T : ℝ) := by rw [hTdef]; exact Nat.le_ceil _
  have hstep : E2 * (T : ℝ) * (t / (T : ℝ)) ^ 2 ≤ ε := by
    refine step_count_budget_suffices E2 (t / (T : ℝ)) t ε T hε hT0 ?_ hTge
    have hTne : (T : ℝ) ≠ 0 := hT0.ne'
    field_simp
  have hcge : E2 * t * (t / (T : ℝ)) * (m : ℝ) ^ 2 / ε ≤ (c : ℝ) := by
    rw [hcdef]; exact Nat.le_ceil _
  have hcn : c ≤ n := by rw [hndef]; omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have hn1 : 1 ≤ n := by
      rw [hndef]
      have := hm
      omega
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hcopy : E2 * t * (t / (T : ℝ)) * (m : ℝ) ^ 2 / (n : ℝ) ≤ ε := by
    refine copy_denominator_budget E2 (t / (T : ℝ)) t (m : ℝ) (n : ℝ) ε hε hnpos ?_
    exact le_trans hcge (by exact_mod_cast hcn)
  refine ⟨T, n, hTpos, ?_, hstep, hcopy⟩
  rw [hndef]
  omega

end Qatlib.Papers.NonlinearDE20.Resources.Joint
