/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.DyadicFloor.FloorRounding.RationalRoundingDefs

/-!
# Error bounds for rational dyadic floor rounding

`floorDyadic` rounds rationals downward at a chosen binary precision. This module bounds its
error by one grid spacing and identifies its real interpretation. Such finite-precision
estimates supply elementary rounding tools for semidefinite-programming settings such as
[BrandaoSvore2017].

## Main statements

* `error_nonneg`: the rounding error is nonnegative.
* `error_lt`: the error is strictly below one dyadic grid spacing.
* `cast_floor`: rational rounding agrees with the stated real floor formula.
* `g1`: the combined rounding guarantees.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.DyadicFloor.FloorRounding
open Qatlib.Concepts.DyadicFloor.FloorRounding

/-- Every natural power of two is positive in the rationals. -/
lemma two_pow_pos (p : ℕ) : 0 < (2 : ℚ) ^ p := by
  exact pow_pos (by norm_num) p

/-- Dyadic floor rounding never exceeds the original rational number. -/
lemma error_nonneg (p : ℕ) (x : ℚ) : 0 ≤ x - floorDyadic p x := by
  unfold floorDyadic
  have h2 := two_pow_pos p
  have hle : ((⌊x * (2 : ℚ) ^ p⌋ : ℤ) : ℚ) ≤ x * (2 : ℚ) ^ p := Int.floor_le _
  rw [sub_nonneg]
  exact (div_le_iff₀ h2).mpr hle

/-- The error of dyadic floor rounding at precision `p` is strictly less than `1 / 2 ^ p`. -/
lemma error_lt (p : ℕ) (x : ℚ) : x - floorDyadic p x < 1 / (2 : ℚ) ^ p := by
  unfold floorDyadic
  have h2 := two_pow_pos p
  have hlt : x * (2 : ℚ) ^ p < ((⌊x * (2 : ℚ) ^ p⌋ : ℤ) : ℚ) + 1 := Int.lt_floor_add_one _
  rw [sub_lt_iff_lt_add]
  have hsplit : (((⌊x * (2 : ℚ) ^ p⌋ : ℤ) : ℚ) + 1) / (2 : ℚ) ^ p =
      1 / (2 : ℚ) ^ p + ((⌊x * (2 : ℚ) ^ p⌋ : ℤ) : ℚ) / (2 : ℚ) ^ p := by
    field_simp [h2.ne']
    ring
  rw [← hsplit]
  exact (lt_div_iff₀ h2).mpr hlt

/-- Casting rational dyadic floor rounding to the reals gives the corresponding real floor
formula. -/
lemma cast_floor (p : ℕ) (x : ℚ) :
    (floorDyadic p x : ℝ) = (⌊(x : ℝ) * (2 : ℝ) ^ p⌋ : ℝ) / (2 : ℝ) ^ p := by
  unfold floorDyadic
  have hfloor : ⌊(2 : ℚ) ^ p * x⌋ = ⌊(2 : ℝ) ^ p * (x : ℝ)⌋ := by
    norm_cast
  rw [mul_comm x, mul_comm (x : ℝ), Rat.cast_div, Rat.cast_intCast, Rat.cast_pow, hfloor]
  have h2 : ((2 : ℚ) : ℝ) = 2 := by norm_cast
  rw [h2]

/-- Dyadic floor rounding has nonnegative error below `1 / 2 ^ p` and commutes with the stated
real floor interpretation. -/
theorem g1 :
    ∀ (p : ℕ) (x : ℚ),
      0 ≤ x - floorDyadic p x ∧ x - floorDyadic p x < 1 / (2 : ℚ) ^ p ∧
      (floorDyadic p x : ℝ) = (⌊(x : ℝ) * (2 : ℝ) ^ p⌋ : ℝ) / (2 : ℝ) ^ p := by
  intro p x
  exact ⟨error_nonneg p x, error_lt p x, cast_floor p x⟩

end Qatlib.Concepts.DyadicFloor.FloorRounding
