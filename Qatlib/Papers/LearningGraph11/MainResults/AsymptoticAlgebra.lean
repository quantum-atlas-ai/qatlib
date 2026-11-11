/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

set_option backward.isDefEq.respectTransparency false

/-!
# LearningGraph11: real-power bookkeeping for Theorems 9-11

Fixed source: arXiv:1109.5135v1, Sections 4.2-4.3 (pp. 14-16).

The complexity analyses of Theorems 9, 10 and 11 multiply and compare powers of the
input size `n ≥ 1`. This file collects the elementary `Real.rpow` bookkeeping used to
combine stage costs into a single power and to compare two exponent bounds.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LearningGraph11.MainResults

/-- `n^a · n^b · n^c = n^(a+b+c)` for a positive base. -/
theorem rpow_mul_three {n : ℝ} (hn : 0 < n) (a b c : ℝ) :
    n ^ a * n ^ b * n ^ c = n ^ (a + b + c) := by
  rw [← Real.rpow_add hn a b, ← Real.rpow_add hn (a + b) c]

/-- `n^a · n^b · n^c · n^d = n^(a+b+c+d)` for a positive base. -/
theorem rpow_mul_four {n : ℝ} (hn : 0 < n) (a b c d : ℝ) :
    n ^ a * n ^ b * n ^ c * n ^ d = n ^ (a + b + c + d) := by
  rw [← Real.rpow_add hn a b, ← Real.rpow_add hn (a + b) c,
    ← Real.rpow_add hn (a + b + c) d]

/-- For base `n > 1`, the minimum of two powers is the power of the minimum exponent. -/
theorem rpow_min {n : ℝ} (hn : 1 < n) (a b : ℝ) :
    min (n ^ a) (n ^ b) = n ^ (min a b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (Real.rpow_le_rpow_of_exponent_le hn.le h)]
  · rw [min_eq_right h, min_eq_right (Real.rpow_le_rpow_of_exponent_le hn.le h)]

/-- Subtracting the larger of two numbers gives the smaller difference. -/
theorem min_sub_max (A t₁ t₂ : ℝ) : min (A - t₁) (A - t₂) = A - max t₁ t₂ := by
  rcases le_total t₁ t₂ with h | h
  · rw [max_eq_right h, min_eq_right (by linarith)]
  · rw [max_eq_left h, min_eq_left (by linarith)]

end Qatlib.Papers.LearningGraph11.MainResults
