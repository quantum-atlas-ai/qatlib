/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.MPFRootStep
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.MPFSegments

def rootFactor (z A ε : ℝ) (m : ℕ) : ℝ :=
  (1 + 8 * Real.pi * z * A / ε) ^ (((2 * m : ℕ) : ℝ)⁻¹)

def count (z A ε : ℝ) (m : ℕ) : ℕ := max 1 (Nat.ceil (2 * z * rootFactor z A ε m))

theorem count_pos (z A ε : ℝ) (m : ℕ) : 0 < count z A ε m := by
  exact lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _)

theorem rootFactor_one_le (z A ε : ℝ) (m : ℕ) (hz : 0 ≤ z) (hA : 0 ≤ A) (hε : 0 < ε) :
    1 ≤ rootFactor z A ε m := by
  apply Real.one_le_rpow
  · have h : 0 ≤ 8 * Real.pi * z * A / ε := by positivity
    linarith
  · positivity

theorem rootFactor_pow (z A ε : ℝ) (m : ℕ) (hm : 0 < m)
    (hz : 0 ≤ z) (hA : 0 ≤ A) (hε : 0 < ε) :
    rootFactor z A ε m ^ (2 * m) = 1 + 8 * Real.pi * z * A / ε :=
  Real.rpow_inv_natCast_pow (by positivity) (by omega)

theorem count_lower (z A ε : ℝ) (m : ℕ) :
    2 * z * rootFactor z A ε m ≤ (count z A ε m : ℝ) :=
  (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 (Nat.ceil (2 * z * rootFactor z A ε m))))

theorem count_eq_ceil (z A ε : ℝ) (m : ℕ) (hz : 0 < z) (hA : 0 ≤ A) (hε : 0 < ε) :
    count z A ε m = Nat.ceil (2 * z * rootFactor z A ε m) := by
  have hr : 0 < 2 * z * rootFactor z A ε m :=
    mul_pos (by positivity) (lt_of_lt_of_le zero_lt_one (rootFactor_one_le z A ε m hz.le hA hε))
  exact max_eq_right (Nat.succ_le_iff.mpr (Nat.ceil_pos.mpr hr))

theorem count_zero (A ε : ℝ) (m : ℕ) : count 0 A ε m = 1 := by
  simp [count]

theorem count_upper (z A ε : ℝ) (m : ℕ) (hz : 0 ≤ z) (hA : 0 ≤ A) (hε : 0 < ε) :
    (count z A ε m : ℝ) ≤ 2 * z * rootFactor z A ε m + 1 := by
  by_cases hz0 : z = 0
  · subst z
    rw [count_zero]
    norm_num
  · rw [count_eq_ceil z A ε m (lt_of_le_of_ne hz (Ne.symm hz0)) hA hε]
    have hR := rootFactor_one_le z A ε m hz hA hε
    exact (Nat.ceil_lt_add_one (by positivity : 0 ≤ 2 * z * rootFactor z A ε m)).le

theorem scaled_step (z A ε : ℝ) (m : ℕ) :
    (z / (count z A ε m : ℝ)) * rootFactor z A ε m ≤ 1 / 2 := by
  have hr : 0 < (count z A ε m : ℝ) := by exact_mod_cast count_pos z A ε m
  calc
    _ = (z * rootFactor z A ε m) / (count z A ε m : ℝ) := by ring
    _ ≤ 1 / 2 := (div_le_iff₀ hr).mpr (by linarith [count_lower z A ε m])

theorem step_control (z A ε : ℝ) (m : ℕ) (hz : 0 ≤ z) (hA : 0 ≤ A) (hε : 0 < ε) :
    z / (count z A ε m : ℝ) ≤ 1 / 2 := by
  have hr : 0 ≤ z / (count z A ε m : ℝ) := by positivity
  exact (le_mul_of_one_le_right hr (rootFactor_one_le z A ε m hz hA hε)).trans
    (scaled_step z A ε m)

theorem accumulated_local (z A ε : ℝ) (m : ℕ) (hm : 0 < m)
    (hz : 0 ≤ z) (hA : 0 ≤ A) (hε : 0 < ε) :
    (count z A ε m : ℝ) * ((8 / 3 : ℝ) * A * (z / (count z A ε m : ℝ)) ^ (2 * m + 1)) ≤
      ε / (12 * Real.pi) := by
  let r : ℝ := count z A ε m
  let b := z / r
  let R := rootFactor z A ε m
  let B := 1 + 8 * Real.pi * z * A / ε
  have hr : 0 < r := by
    change 0 < (count z A ε m : ℝ)
    exact_mod_cast count_pos z A ε m
  have hb : 0 ≤ b := div_nonneg hz hr.le
  have hR : 0 ≤ R := (rootFactor_one_le z A ε m hz hA hε).trans' (by norm_num)
  have hB : 0 < B := by dsimp [B]; positivity
  have hpow : b ^ (2 * m) * B ≤ 1 / 4 := by
    have h := pow_le_pow_left₀ (mul_nonneg hb hR) (scaled_step z A ε m) (2 * m)
    rw [mul_pow, rootFactor_pow z A ε m hm hz hA hε] at h
    have hsmall : (1 / 2 : ℝ) ^ (2 * m) ≤ (1 / 2 : ℝ) ^ 2 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    exact h.trans (by norm_num at hsmall ⊢; exact hsmall)
  have hscale : r * b ^ (2 * m + 1) = z * b ^ (2 * m) := by
    rw [pow_succ]
    dsimp [b]
    field_simp
  have hbudget : (r * ((8 / 3 : ℝ) * A * b ^ (2 * m + 1))) * B ≤ (2 / 3 : ℝ) * A * z := by
    calc
      _ = ((8 / 3 : ℝ) * A * B) * (r * b ^ (2 * m + 1)) := by ring
      _ = ((8 / 3 : ℝ) * A * z) * (b ^ (2 * m) * B) := by rw [hscale]; ring
      _ ≤ ((8 / 3 : ℝ) * A * z) * (1 / 4) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by ring
  have hright : (2 / 3 : ℝ) * A * z ≤ (ε / (12 * Real.pi)) * B := by
    have he : (ε / (12 * Real.pi)) * B = ε / (12 * Real.pi) + (2 / 3 : ℝ) * A * z := by
      dsimp [B]
      field_simp
      ring
    rw [he]
    exact le_add_of_nonneg_left (by positivity)
  exact (mul_le_mul_iff_left₀ hB).mp (hbudget.trans hright)

end Qatlib.Papers.CommutLCHS26.MainResults.MPFSegments
