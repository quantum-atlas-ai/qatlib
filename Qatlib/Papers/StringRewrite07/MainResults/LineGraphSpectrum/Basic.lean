/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.StringRewrite07.MainResults.Source

/-!
# Endpoint symmetries of path spectral formulas

`lineEigenvalue` defines the cosine spectrum formula, `lineEigvecEntry` the normalized sine
formula, and `lineWeight` the endpoint product. The file proves sign relations between the first
and last spectral terms, which make their weighted powers equal when the exponent has the
required parity. See [JanzingWocjan2010].

## Main statements

* `lineEigenvalue_last`: the last eigenvalue formula is the negative of the first.
* `lineWeight_last`: the endpoint weights differ by the sign `(-1) ^ (ℓ - 1)`.
* `lineGraph_dominant_term_eq`: the two extreme weighted powers agree under the parity
  condition.

## References

* [Janzing and Wocjan, 2010][JanzingWocjan2010]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.StringRewrite07.MainResults

/-- The path spectral value `2 * cos (π * (j + 1) / (ℓ + 1))`. -/
def lineEigenvalue (ℓ j : ℕ) : ℝ :=
  2 * Real.cos (Real.pi * ((j : ℝ) + 1) / ((ℓ : ℝ) + 1))

/-- The sine-form path vector entry `sqrt (2 / (ℓ + 1)) * sin (π * (j + 1) * (k + 1) / (ℓ +
1))`. -/
def lineEigvecEntry (ℓ j k : ℕ) : ℝ :=
  Real.sqrt (2 / ((ℓ : ℝ) + 1)) *
    Real.sin (Real.pi * ((j : ℝ) + 1) * ((k : ℝ) + 1) / ((ℓ : ℝ) + 1))

/-- The product of the sine-form vector entries at positions zero and `ℓ - 1`. -/
def lineWeight (ℓ j : ℕ) : ℝ :=
  lineEigvecEntry ℓ j 0 * lineEigvecEntry ℓ j (ℓ - 1)

/-- For positive `ℓ`, casting its natural predecessor to the reals and adding one gives `ℓ`. -/
theorem cast_pred_add_one {ℓ : ℕ} (hℓ : 0 < ℓ) :
    ((ℓ - 1 : ℕ) : ℝ) + 1 = (ℓ : ℝ) := by
  have h : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.succ_le_of_lt hℓ), Nat.cast_one]
  rw [h]; ring_nf

/-- For positive `ℓ`, the spectral value at index `ℓ - 1` is the negative of the value at index
zero. See [JanzingWocjan2010]. -/
theorem lineEigenvalue_last {ℓ : ℕ} (hℓ : 0 < ℓ) :
    lineEigenvalue ℓ (ℓ - 1) = - lineEigenvalue ℓ 0 := by
  have hidx := cast_pred_add_one (ℓ := ℓ) hℓ
  have hzero : ((0 : ℕ) : ℝ) + 1 = 1 := by norm_num
  unfold lineEigenvalue
  rw [hidx, hzero]
  have harg : Real.pi * (ℓ : ℝ) / ((ℓ : ℝ) + 1)
      = Real.pi - Real.pi / ((ℓ : ℝ) + 1) := by
    have hden : ((ℓ : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring_nf
  rw [harg, Real.cos_pi_sub]
  ring_nf

/-- For positive `ℓ`, `sin (π * ℓ² / (ℓ + 1))` equals `(-1) ^ (ℓ - 1) * sin (π / (ℓ + 1))`. -/
theorem sin_pi_sq {ℓ : ℕ} (hℓ : 0 < ℓ) :
    Real.sin (Real.pi * (ℓ : ℝ) * (ℓ : ℝ) / ((ℓ : ℝ) + 1))
      = (-1 : ℝ) ^ (ℓ - 1) * Real.sin (Real.pi / ((ℓ : ℝ) + 1)) := by
  have hcast : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.succ_le_of_lt hℓ), Nat.cast_one]
  have harg : Real.pi * (ℓ : ℝ) * (ℓ : ℝ) / ((ℓ : ℝ) + 1)
      = Real.pi / ((ℓ : ℝ) + 1) + ((ℓ - 1 : ℕ) : ℝ) * Real.pi := by
    have hden : ((ℓ : ℝ) + 1) ≠ 0 := by positivity
    rw [hcast]
    field_simp
    ring_nf
  rw [harg, Real.sin_add_nat_mul_pi]

/-- For positive `ℓ`, the last endpoint weight is `(-1) ^ (ℓ - 1)` times the first endpoint
weight. See [JanzingWocjan2010]. -/
theorem lineWeight_last {ℓ : ℕ} (hℓ : 0 < ℓ) :
    lineWeight ℓ (ℓ - 1) = (-1 : ℝ) ^ (ℓ - 1) * lineWeight ℓ 0 := by
  have hidx := cast_pred_add_one (ℓ := ℓ) hℓ
  have hzero : ((0 : ℕ) : ℝ) + 1 = 1 := by norm_num
  unfold lineWeight lineEigvecEntry
  rw [hidx, hzero]
  rw [sin_pi_sq hℓ]
  simp only [mul_one]
  ring_nf

/-- If `m` and `ℓ - 1` have the same parity and `ℓ > 0`, then the first and last weighted
eigenvalue powers are equal. See [JanzingWocjan2010]. -/
theorem lineGraph_dominant_term_eq {ℓ : ℕ} (hℓ : 0 < ℓ) (m : ℕ) (hm : m % 2 = (ℓ - 1) % 2) :
    (lineEigenvalue ℓ (ℓ - 1)) ^ m * lineWeight ℓ (ℓ - 1)
      = (lineEigenvalue ℓ 0) ^ m * lineWeight ℓ 0 := by
  have hlam := lineEigenvalue_last hℓ
  have hw : lineWeight ℓ (ℓ - 1) = (-1 : ℝ) ^ m * lineWeight ℓ 0 := by
    rw [lineWeight_last hℓ]
    have hpow : ((-1 : ℝ) ^ (ℓ - 1)) = (-1 : ℝ) ^ m := by
      rw [neg_one_pow_eq_pow_mod_two (ℓ - 1), neg_one_pow_eq_pow_mod_two m, hm]
    rw [hpow]
  exact dom_weight_eq hlam hw

end Qatlib.Papers.StringRewrite07.MainResults
