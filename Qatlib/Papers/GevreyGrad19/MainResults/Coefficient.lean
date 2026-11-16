/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GevreyGrad19.MainResults.Model.GevreyGradDefinitions
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section


/-!
# Complete central-difference source bounds

Bridges the public binomial-coefficient model to arXiv:1909.13528v1,
Definition 3.3 and Theorem 3.4, without extra mathematical assumptions.
-/

set_option autoImplicit false

namespace Qatlib.Papers.GevreyGrad19.MainResults

open Qatlib.Papers.GevreyGrad19.MainResults
open Qatlib.Concepts.GradientOracle.CentralDiff

/-- A positive lower index makes the binomial coefficient strictly increase after a positive shift. -/
theorem choose_lt_shift {m k : ℕ} (hk : 0 < k) (hkm : k ≤ m) :
    m.choose k < (m + k).choose k := by
  calc
    m.choose k < (m + 1).choose k := by
      cases k with
      | zero => omega
      | succ j =>
        rw [Nat.choose_succ_succ]
        have := Nat.choose_pos (by omega : j ≤ m)
        simp only [Nat.succ_eq_add_one] at *
        omega
    _ ≤ (m + k).choose k := Nat.choose_le_choose k (by omega)

/-- At a positive index the binomial definition equals the factorial quotient. -/
theorem coefficient_nat (m k : ℕ) (hk : 0 < k) (hkm : k ≤ m) :
    paperCentralCoeff m (k : ℤ) =
      (-1 : ℝ) ^ (k - 1) * ((m.factorial : ℝ) ^ 2) /
        ((k : ℝ) * ((m + k).factorial : ℝ) * ((m - k).factorial : ℝ)) := by
  have hkz : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [paperCentralCoeff, ite_eq_right hkz, centralDiffCoeff, ite_eq_right hkz]
  simp only [Int.natAbs_natCast, Int.cast_natCast]
  rw [Nat.cast_choose ℝ hkm, Nat.cast_choose ℝ (by omega : k ≤ m + k)]
  rw [Nat.add_sub_cancel_right]
  have hf : ∀ j : ℕ, (j.factorial : ℝ) ≠ 0 := fun j => by
    exact_mod_cast Nat.factorial_ne_zero j
  field_simp [hf]

end Qatlib.Papers.GevreyGrad19.MainResults
