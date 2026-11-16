/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section


/-! # Exact integer optimization of a linear plus reciprocal cost

The neighboring thresholds k(k-1) and k(k+1) certify a global positive
integer minimum. They replace an unjustified nearest-integer rule for the
continuous minimizer. Source: HamEfficiency10, Section IV.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Foundations.DiscreteOptim.ReciprocalCost.IntegerChoice

/-- The logarithmic order-dependent cost, with an irrelevant fixed additive constant omitted. -/
def cost (a b : ℝ) (k : ℕ) : ℝ := a * ((k : ℝ) - 1) + b / (k : ℝ)

/-- Clearing the positive integer denominators factors the complete cost difference. -/
theorem difference (a b : ℝ) {j k : ℕ} (hj : 0 < j) (hk : 0 < k) :
    (cost a b j - cost a b k) * ((j : ℝ) * (k : ℝ)) =
      ((j : ℝ) - (k : ℝ)) * (a * (j : ℝ) * (k : ℝ) - b) := by
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold cost
  field_simp [hj0, hk0]
  ring

/-- Two adjacent threshold inequalities certify a global minimum over every positive integer. -/
theorem globalMin {a b : ℝ} (ha : 0 ≤ a) {k : ℕ} (hk : 0 < k)
    (hleft : a * ((k : ℝ) - 1) * (k : ℝ) ≤ b)
    (hright : b ≤ a * (k : ℝ) * ((k : ℝ) + 1)) :
    ∀ j : ℕ, 0 < j → cost a b k ≤ cost a b j := by
  intro j hj
  have hjr : 0 < (j : ℝ) := by exact_mod_cast hj
  have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
  have hprod : 0 < (j : ℝ) * (k : ℝ) := mul_pos hjr hkr
  have hval : 0 ≤ (cost a b j - cost a b k) * ((j : ℝ) * (k : ℝ)) := by
    rw [difference a b hj hk]
    rcases lt_trichotomy j k with hlt | heq | hgt
    · have hdiff : (j : ℝ) ≤ (k : ℝ) - 1 := by
        have hnat : j + 1 ≤ k := hlt
        have hn : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hnat
        linarith
      have hmul := mul_le_mul_of_nonneg_right hdiff (mul_nonneg ha hkr.le)
      have hsign : a * (j : ℝ) * (k : ℝ) - b ≤ 0 := by nlinarith
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) hsign
    · simp [heq]
    · have hdiff : (k : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hgt
      have hmul := mul_le_mul_of_nonneg_right hdiff (mul_nonneg ha hkr.le)
      have hsign : 0 ≤ a * (j : ℝ) * (k : ℝ) - b := by nlinarith
      exact mul_nonneg (by linarith) hsign
  apply (mul_le_mul_iff_of_pos_right hprod).mp
  nlinarith

/-- The genuine adjacent-candidate tie occurs at b=a*k*(k+1), not at a rounding midpoint. -/
theorem adjacentTie (a : ℝ) {k : ℕ} (hk : 0 < k) :
    cost a (a * (k : ℝ) * ((k : ℝ) + 1)) k =
      cost a (a * (k : ℝ) * ((k : ℝ) + 1)) (k + 1) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  simp only [cost, Nat.cast_add, Nat.cast_one]
  field_simp [hk0, hk1]
  ring

end Qatlib.Foundations.DiscreteOptim.ReciprocalCost.IntegerChoice
