/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic

/-!
# Recursive oracle-query counts

This module compares the doubling recurrences `queryRec` and `classicalRec` and proves that both
equal `2^r`. It also records that distinct input-dependent phase factors cannot be represented
by one constant multiplier of a fixed nonzero amplitude. The construction follows
[Jordan2005Gradient].

## Main statements

* `inputDependentPhase_not_global`: rules out a constant multiplier for all phases.
* `recursion_matches_classical`: identifies the two recursive query counts.

## References

* [Jordan, 2005][Jordan2005Gradient]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.FastGradEst04.HigherOracle

/-- For nonzero amplitude and two distinct phase factors, no single constant multiplier
represents the amplitude times every phase factor. -/
theorem inputDependentPhase_not_global (A : ℂ) (φ₁ φ₂ : ℝ) (hA : A ≠ 0)
    (hne : Complex.exp (φ₁ * Complex.I) ≠ Complex.exp (φ₂ * Complex.I)) :
    ¬ ∃ c : ℂ, ∀ φ : ℝ, A * Complex.exp (φ * Complex.I) = c * A := by
  rintro ⟨c, hc⟩
  have h1 := hc φ₁
  have h2 := hc φ₂
  have heq : A * Complex.exp (φ₁ * Complex.I) = A * Complex.exp (φ₂ * Complex.I) := by
    rw [h1, h2]
  exact hne (mul_left_cancel₀ hA heq)

/-- The recursive query count starting at one and doubling at each level. -/
def queryRec : ℕ → ℕ
  | 0 => 1
  | r + 1 => 2 * queryRec r

/-- The recursive query count at level `r` is `2^r`. -/
theorem recursionQueries_eq (r : ℕ) : queryRec r = 2 ^ r := by
  induction r with
  | zero => simp [queryRec]
  | succ k ih =>
    rw [queryRec, ih, pow_succ]
    ring

/-- The classical comparison count starting at one and doubling at each level. -/
def classicalRec : ℕ → ℕ
  | 0 => 1
  | r + 1 => 2 * classicalRec r

/-- The classical comparison count at level `r` is `2^r`. -/
theorem classicalQueries_eq (r : ℕ) : classicalRec r = 2 ^ r := by
  induction r with
  | zero => simp [classicalRec]
  | succ k ih =>
    rw [classicalRec, ih, pow_succ]
    ring

/-- The recursive and classical comparison counts coincide at every level. -/
theorem recursion_matches_classical (r : ℕ) : queryRec r = classicalRec r := by
  rw [recursionQueries_eq, classicalQueries_eq]

/-- The recursive query count is positive at every level. -/
theorem queryRec_pos (r : ℕ) : 0 < queryRec r := by
  rw [recursionQueries_eq]
  positivity

end Qatlib.Papers.FastGradEst04.HigherOracle
