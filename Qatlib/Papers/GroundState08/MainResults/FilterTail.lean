/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# Parameter budget for the energy-filter tail

Appendix C, Eq. (C15) of arXiv:0809.2705 gives a scalar sufficient condition
on precision and filter repetitions. Taking logarithms allows a finite
comparison even when the parameters are natural numbers.
-/

set_option autoImplicit false

namespace Qatlib.Papers.GroundState08.MainResults

/-- The precision and repetition choices in Appendix C bound the upper-tail expression
of Eq. (C15) by half the requested energy tolerance. -/
theorem appendixC_tail_bound (n k η : ℕ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hk : (ε⁻¹) ^ 2 ≤ (2 : ℝ) ^ k)
    (hη : 1 + ((n : ℝ) + 1) / Real.logb 2 ε⁻¹ ≤ (η : ℝ)) :
    ((2 : ℝ) ^ n) ^ 2 / ((2 : ℝ) ^ k * ε) ^ (2 * η) ≤ ε / 2 := by
  have hInv : 1 < ε⁻¹ := (one_lt_inv₀ hε0).2 hε1
  have hInv0 : 0 < ε⁻¹ := inv_pos.mpr hε0
  have hlog : 0 < Real.log ε⁻¹ := Real.log_pos hInv
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hηlog : ((n : ℝ) + 1) * Real.log 2 ≤ ((η : ℝ) - 1) * Real.log ε⁻¹ := by
    apply (div_le_iff₀ hlog).1
    rw [← div_div_eq_mul_div]
    unfold Real.logb at hη
    linarith only [hη]
  have hbase : ε⁻¹ ≤ (2 : ℝ) ^ k * ε := calc
    ε⁻¹ = (ε⁻¹) ^ 2 * ε := by field_simp [hε0.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_right hk hε0.le
  have hprod : ((2 : ℝ) ^ n) ^ 2 * (2 * ε⁻¹) ≤ (ε⁻¹) ^ (2 * η) := by
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
      Real.log_mul (by norm_num) hInv0.ne', Real.log_pow]
    push_cast
    nlinarith only [hlog, hlog2, hηlog]
  apply (div_le_iff₀ (by positivity)).2
  calc
    ((2 : ℝ) ^ n) ^ 2 = (ε / 2) * (((2 : ℝ) ^ n) ^ 2 * (2 * ε⁻¹)) := by
      field_simp [hε0.ne']
    _ ≤ (ε / 2) * (ε⁻¹) ^ (2 * η) := mul_le_mul_of_nonneg_left hprod (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hInv0.le hbase _) (by positivity)

/-- The printed logarithmic precision condition implies the power bound in Eq. (C15). -/
theorem appendixC_tail_bound_log (n k η : ℕ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hk : 2 * Real.logb 2 ε⁻¹ ≤ (k : ℝ))
    (hη : 1 + ((n : ℝ) + 1) / Real.logb 2 ε⁻¹ ≤ (η : ℝ)) :
    ((2 : ℝ) ^ n) ^ 2 / ((2 : ℝ) ^ k * ε) ^ (2 * η) ≤ ε / 2 := by
  apply appendixC_tail_bound n k η hε0 hε1 _ hη
  have hInv : 0 < ε⁻¹ := inv_pos.mpr hε0
  have hlog : Real.logb 2 ((ε⁻¹) ^ 2) ≤ (k : ℝ) := by
    rw [Real.logb, Real.log_pow, Nat.cast_ofNat, mul_div_assoc]
    exact hk
  have hp := (Real.logb_le_iff_le_rpow (b := 2) (by norm_num)
    (show 0 < (ε⁻¹) ^ 2 from pow_pos hInv 2)).1 hlog
  rwa [Real.rpow_natCast] at hp

end Qatlib.Papers.GroundState08.MainResults
