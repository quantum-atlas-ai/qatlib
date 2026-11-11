/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Abelian stabilizer sampling parameters

This module defines the sample count `aspSampleCount n = n + 4` and per-coordinate precision
`aspEpsilon k n = 1 / (6 * k * (n + 4))` used in the Abelian stabilizer algorithm. It proves
positivity for positive `k` and that the precision parameter decreases when `k` increases.

The mathematical background is discussed in [Kitaev1995].

## Main statements

* `aspSampleCount`: the prescribed number of samples.
* `aspEpsilon_pos`: positivity of the precision parameter for positive `k`.
* `aspEpsilon_antitone`: monotonic decrease in the coordinate count.

## References

* [Kitaev, 1995][Kitaev1995]
-/

set_option autoImplicit false
namespace Qatlib.Papers.AbelianStabil95.AbelianStabil.AspAlgorithm

/-- The sample count `n + 4` for the Abelian stabilizer algorithm. -/
def aspSampleCount (n : ℕ) : ℕ := n + 4

/-- The per-coordinate error parameter `1 / (6 * k * aspSampleCount n)`. -/
noncomputable def aspEpsilon (k n : ℕ) : ℝ :=
  (6 * (k : ℝ) * (aspSampleCount n : ℝ))⁻¹

/-- The per-coordinate error parameter is strictly positive whenever `k` is positive. See
[Kitaev1995]. -/
theorem aspEpsilon_pos {k n : ℕ} (hk : 0 < k) : 0 < aspEpsilon k n := by
  unfold aspEpsilon aspSampleCount
  push_cast
  have : (0 : ℝ) < 6 * (k : ℝ) * ((n : ℝ) + 4) := by positivity
  exact inv_pos.mpr this

/-- For positive `k ≤ k'`, the per-coordinate error parameter at `k'` is no greater than the
parameter at `k`. -/
theorem aspEpsilon_antitone {k k' n : ℕ} (hk : 0 < k) (hkk' : k ≤ k') :
    aspEpsilon k' n ≤ aspEpsilon k n := by
  unfold aspEpsilon aspSampleCount
  push_cast
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hk'R : (0 : ℝ) < (k' : ℝ) := by exact_mod_cast lt_of_lt_of_le hk hkk'
  have hkpos : (0 : ℝ) < 6 * (k : ℝ) * ((n : ℝ) + 4) := by positivity
  have hk'pos : (0 : ℝ) < 6 * (k' : ℝ) * ((n : ℝ) + 4) := by positivity
  rw [inv_le_inv₀ hk'pos hkpos]
  have hcast : (k : ℝ) ≤ (k' : ℝ) := by exact_mod_cast hkk'
  have step : 6 * (k : ℝ) ≤ 6 * (k' : ℝ) := by linarith
  exact mul_le_mul_of_nonneg_right step (by positivity)

end Qatlib.Papers.AbelianStabil95.AbelianStabil.AspAlgorithm
