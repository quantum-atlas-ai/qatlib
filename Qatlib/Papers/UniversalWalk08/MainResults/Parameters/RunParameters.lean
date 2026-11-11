/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Walk times and filter repetition counts

This module chooses the runtime and filter count for the quantum-walk construction in
[Childs2009]. The value `walkTime` is a nonnegative integer multiple of `π` close to `(x + l) /
√2`, while `filterCount` is the natural ceiling of `log(m²)`.

## Main statements

* `walkTime_le_two_pow_four`: The quartic parameter choice gives runtime at most `2 * m ^ 4`.
* `bound_state_phases_equal`: The chosen runtime aligns opposite bound-state phases.
* `filterCount_bounds`: The filter count lies between `log(m²)` and `log(m²) + 1`.

## References

* [Childs, 2009][Childs2009]
-/

namespace Qatlib.Papers.UniversalWalk08.MainResults.Parameters

set_option autoImplicit false

/-- The runtime `π` times the natural floor of `(x + l) / (√2 * π)`. -/
noncomputable def walkTime (x l : ℝ) : ℝ :=
  Real.pi * (⌊(x + l) / (Real.sqrt 2 * Real.pi)⌋₊ : ℝ)

/-- If `x + l ≥ 0`, the selected runtime is at most `(x + l) / √2` [Childs2009]. -/
theorem walkTime_le {x l : ℝ} (hxl : 0 ≤ x + l) :
    walkTime x l ≤ (x + l) / Real.sqrt 2 := by
  unfold walkTime
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hq : ((⌊(x + l) / (Real.sqrt 2 * Real.pi)⌋₊ : ℝ)) ≤
      (x + l) / (Real.sqrt 2 * Real.pi) :=
    Nat.floor_le (by positivity)
  calc
    Real.pi * (⌊(x + l) / (Real.sqrt 2 * Real.pi)⌋₊ : ℝ)
        ≤ Real.pi * ((x + l) / (Real.sqrt 2 * Real.pi)) := by gcongr
    _ = (x + l) / Real.sqrt 2 := by
      field_simp

/-- The quantity `(x + l) / √2` is strictly less than the selected runtime plus `π`
[Childs2009]. -/
theorem lt_walkTime_add_pi (x l : ℝ) :
    (x + l) / Real.sqrt 2 < walkTime x l + Real.pi := by
  unfold walkTime
  have hpi : 0 < Real.pi := Real.pi_pos
  have hq : (x + l) / (Real.sqrt 2 * Real.pi) <
      (⌊(x + l) / (Real.sqrt 2 * Real.pi)⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hstep : Real.pi * ((x + l) / (Real.sqrt 2 * Real.pi)) <
      Real.pi * ((⌊(x + l) / (Real.sqrt 2 * Real.pi)⌋₊ : ℝ) + 1) := by
    gcongr
  have heq : Real.pi * ((x + l) / (Real.sqrt 2 * Real.pi)) =
      (x + l) / Real.sqrt 2 := by field_simp
  rw [heq] at hstep
  calc
    (x + l) / Real.sqrt 2
        < Real.pi * ((⌊(x + l) / (Real.sqrt 2 * Real.pi)⌋₊ : ℝ) + 1) := hstep
    _ = walkTime x l + Real.pi := by unfold walkTime; ring

/-- The selected runtime is `π` times the natural floor of `(x + l) / (√2 * π)`. -/
theorem walkTime_eq_pi_mul_nat (x l : ℝ) :
    walkTime x l = Real.pi * ((⌊(x + l) / (Real.sqrt 2 * Real.pi)⌋₊ : ℕ) : ℝ) := rfl

/-- The complex phase at twice a natural multiple of `π` equals one [Childs2009]. -/
theorem exp_two_mul_pi_mul_nat_mul_I (N : ℕ) :
    Complex.exp (((2 * (Real.pi * (N : ℝ)) : ℝ) : ℂ) * Complex.I) = 1 := by
  rw [show 2 * (Real.pi * (N : ℝ)) = (N : ℝ) * (2 * Real.pi) by ring]
  rw [Complex.exp_ofReal_mul_I, Real.cos_nat_mul_two_pi]
  have hsin : Real.sin ((N : ℝ) * (2 * Real.pi)) = 0 := by
    have := Real.sin_add_nat_mul_two_pi (0 : ℝ) N
    simpa using this
  rw [hsin]
  simp

/-- The complex phase at minus twice a natural multiple of `π` equals one [Childs2009]. -/
theorem exp_neg_two_mul_pi_mul_nat_mul_I (N : ℕ) :
    Complex.exp ((-(2 * (Real.pi * (N : ℝ))) : ℝ) * Complex.I) = 1 := by
  rw [show -(2 * (Real.pi * (N : ℝ))) = (((-(N : ℤ)) : ℤ) : ℝ) * (2 * Real.pi) by
    push_cast; ring]
  rw [Complex.exp_ofReal_mul_I, Real.cos_int_mul_two_pi]
  have hsin : Real.sin ((((-(N : ℤ)) : ℤ) : ℝ) * (2 * Real.pi)) = 0 := by
    have := Real.sin_add_int_mul_two_pi (0 : ℝ) (-(N : ℤ))
    simpa using this
  rw [hsin]
  simp

/-- The complex phases of frequencies `2` and `-2` agree at the selected runtime [Childs2009]. -/
theorem bound_state_phases_equal (x l : ℝ) :
    Complex.exp (((2 * walkTime x l : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((-(2 * walkTime x l) : ℝ) : ℂ) * Complex.I) := by
  rw [walkTime_eq_pi_mul_nat]
  rw [exp_two_mul_pi_mul_nat_mul_I, exp_neg_two_mul_pi_mul_nat_mul_I]

/-- For `m ≥ 1`, setting `x = m ^ 4` and `l = m` gives runtime at most `2 * m ^ 4` [Childs2009]. -/
theorem walkTime_le_two_pow_four {m : ℕ} (hm : 1 ≤ m) :
    walkTime ((m : ℝ) ^ 4) (m : ℝ) ≤ 2 * (m : ℝ) ^ 4 := by
  have hxl : 0 ≤ (m : ℝ) ^ 4 + (m : ℝ) := by positivity
  have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm4 : (m : ℝ) ≤ (m : ℝ) ^ 4 := by
    calc (m : ℝ) = (m : ℝ) ^ 1 := by ring
      _ ≤ (m : ℝ) ^ 4 := pow_le_pow_right₀ hm1 (by norm_num : 1 ≤ 4)
  calc walkTime ((m : ℝ) ^ 4) (m : ℝ)
      ≤ ((m : ℝ) ^ 4 + (m : ℝ)) / Real.sqrt 2 := walkTime_le hxl
    _ ≤ ((m : ℝ) ^ 4 + (m : ℝ)) / 1 := by
        gcongr
    _ = (m : ℝ) ^ 4 + (m : ℝ) := by ring
    _ ≤ 2 * (m : ℝ) ^ 4 := by linarith

/-- The natural ceiling of `log(m²)`, used as the number of filter repetitions. -/
noncomputable def filterCount (m : ℕ) : ℕ :=
  ⌈Real.log ((m : ℝ) ^ 2)⌉₊

/-- For `m ≥ 1`, the filter count lies between `log(m²)` and `log(m²) + 1` [Childs2009]. -/
theorem filterCount_bounds {m : ℕ} (hm : 1 ≤ m) :
    Real.log ((m : ℝ) ^ 2) ≤ (filterCount m : ℝ) ∧
      (filterCount m : ℝ) ≤ Real.log ((m : ℝ) ^ 2) + 1 := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hsq : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
  have hlog : 0 ≤ Real.log ((m : ℝ) ^ 2) := Real.log_nonneg hsq
  exact ⟨Nat.le_ceil _, (Nat.ceil_lt_add_one hlog).le⟩

end Qatlib.Papers.UniversalWalk08.MainResults.Parameters
