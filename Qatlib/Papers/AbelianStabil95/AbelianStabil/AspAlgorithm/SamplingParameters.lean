/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false
namespace Qatlib.Papers.AbelianStabil95.AbelianStabil.AspAlgorithm

def aspSampleCount (n : ℕ) : ℕ := n + 4

noncomputable def aspEpsilon (k n : ℕ) : ℝ :=
  (6 * (k : ℝ) * (aspSampleCount n : ℝ))⁻¹

theorem aspEpsilon_pos {k n : ℕ} (hk : 0 < k) : 0 < aspEpsilon k n := by
  unfold aspEpsilon aspSampleCount
  push_cast
  have : (0 : ℝ) < 6 * (k : ℝ) * ((n : ℝ) + 4) := by positivity
  exact inv_pos.mpr this

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
