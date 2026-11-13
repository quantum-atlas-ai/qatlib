/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.FullRange.FullRangeValueGradient

/-!
# Bit-width bounds for full-range value registers

`full_range_classical_bits_guard` proves that the selected classical bit width gives a power of
two strictly above the rational range parameter. For a range at least one,
`full_range_classical_bits_log` compares this width with the ceiling binary logarithm, including
an added precision-bit budget. See [Jordan2005Gradient] for background.

## Main statements

* `full_range_classical_bits_guard`: The power of two specified by `fullRangeClassicalBits A`
  strictly exceeds the rational range parameter `A`.
* `full_range_classical_bits_log`: For `A ≥ 1`, the selected bit width lies between `ceil (logb
  2 A)` and one more, and the same comparison holds after scaling `A` by `2 ^ k` and adding `k`
  bits.

## References

* [Jordan, 2005][Jordan2005Gradient]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.GradientOracle.FullRange

/-- The power of two specified by `fullRangeClassicalBits A` strictly exceeds the rational range
parameter `A`. -/
theorem full_range_classical_bits_guard (A : ℚ) :
    A < (2^fullRangeClassicalBits A : ℕ) := by
  have hb := Nat.le_pow_clog (by norm_num : 1<2) (max 2 (Nat.ceil A+1))
  have hc : Nat.ceil A+1 ≤ 2^fullRangeClassicalBits A :=
    (le_max_right _ _).trans hb
  have hA := Nat.le_ceil A
  have hcast : (Nat.ceil A : ℚ)+1 ≤ (2^fullRangeClassicalBits A : ℕ) := by
    exact_mod_cast hc
  linarith

/-- For `A ≥ 1`, the selected bit width lies between `ceil (logb 2 A)` and one more, and the
same comparison holds after scaling `A` by `2 ^ k` and adding `k` bits. -/
theorem full_range_classical_bits_log (A : ℚ) (hA : 1≤A) :
    let C := Nat.ceil (Real.logb 2 (A:ℝ))
    C≤fullRangeClassicalBits A ∧ fullRangeClassicalBits A≤C+1 ∧
    ∀ k : ℕ,
      Nat.ceil (Real.logb 2 ((A:ℝ)*(2:ℝ)^k))≤fullRangeClassicalBits A+k ∧
      fullRangeClassicalBits A+k≤Nat.ceil (Real.logb 2 ((A:ℝ)*(2:ℝ)^k))+1 := by
  let C := Nat.ceil (Real.logb 2 (A:ℝ))
  have hAr : (1:ℝ)≤A := by exact_mod_cast hA
  have hpos : (0:ℝ)<A := by linarith
  have hbase : (1:ℝ)<2 := by norm_num
  have hlog : 0≤Real.logb 2 (A:ℝ) := Real.logb_nonneg hbase hAr
  have hpow : (A:ℝ)≤(2:ℝ)^C := by
    have h := (Real.logb_le_iff_le_rpow hbase hpos).mp (Nat.le_ceil (Real.logb 2 (A:ℝ)))
    simpa only [Real.rpow_natCast] using! h
  have hceil : Nat.ceil A≤2^C := by
    apply Nat.ceil_le.mpr
    exact_mod_cast hpow
  have hlow : C≤fullRangeClassicalBits A := by
    apply Nat.ceil_le.mpr
    apply (Real.logb_le_iff_le_rpow hbase hpos).mpr
    rw [Real.rpow_natCast]
    exact_mod_cast (full_range_classical_bits_guard A).le
  have hhigh : fullRangeClassicalBits A≤C+1 := by
    apply Nat.clog_le_of_le_pow
    apply max_le
    · have hp : 0<2^C := by positivity
      rw [pow_succ]
      omega
    · rw [pow_succ]
      have hp : 0<2^C := by positivity
      omega
  refine ⟨hlow,hhigh,?_⟩
  intro k
  have he : Nat.ceil (Real.logb 2 ((A:ℝ)*(2:ℝ)^k))=C+k := by
    rw [Real.logb_mul hpos.ne' (by positivity),Real.logb_pow,Real.logb_self_eq_one hbase,
      mul_one,Nat.ceil_add_natCast hlog]
  rw [he]
  omega

end Qatlib.Concepts.GradientOracle.FullRange
