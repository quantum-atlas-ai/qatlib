/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.FastGradEst04.HigherOracle

theorem inputDependentPhase_not_global (A : ℂ) (φ₁ φ₂ : ℝ) (hA : A ≠ 0)
    (hne : Complex.exp (φ₁ * Complex.I) ≠ Complex.exp (φ₂ * Complex.I)) :
    ¬ ∃ c : ℂ, ∀ φ : ℝ, A * Complex.exp (φ * Complex.I) = c * A := by
  rintro ⟨c, hc⟩
  have h1 := hc φ₁
  have h2 := hc φ₂
  have heq : A * Complex.exp (φ₁ * Complex.I) = A * Complex.exp (φ₂ * Complex.I) := by
    rw [h1, h2]
  exact hne (mul_left_cancel₀ hA heq)

def queryRec : ℕ → ℕ
  | 0 => 1
  | r + 1 => 2 * queryRec r

theorem recursionQueries_eq (r : ℕ) : queryRec r = 2 ^ r := by
  induction r with
  | zero => simp [queryRec]
  | succ k ih =>
    rw [queryRec, ih, pow_succ]
    ring

def classicalRec : ℕ → ℕ
  | 0 => 1
  | r + 1 => 2 * classicalRec r

theorem classicalQueries_eq (r : ℕ) : classicalRec r = 2 ^ r := by
  induction r with
  | zero => simp [classicalRec]
  | succ k ih =>
    rw [classicalRec, ih, pow_succ]
    ring

theorem recursion_matches_classical (r : ℕ) : queryRec r = classicalRec r := by
  rw [recursionQueries_eq, classicalQueries_eq]

theorem queryRec_pos (r : ℕ) : 0 < queryRec r := by
  rw [recursionQueries_eq]
  positivity

end Qatlib.Papers.FastGradEst04.HigherOracle
