/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.GradientOracle.StepSizes

def quantumDerivativeError (l D2 : ℝ) (d : ℕ) : ℝ :=
  l * D2 * Real.sqrt d / (2 * Real.sqrt 3)

def classicalTruncationError (D3 l : ℝ) : ℝ := D3 * l ^ 2 / 24

def quantumStep (D2 σ : ℝ) (d : ℕ) : ℝ :=
  2 * Real.sqrt 3 * σ / (D2 * Real.sqrt d)

def classicalStep (D3 σ : ℝ) : ℝ := Real.sqrt (24 * σ / D3)

theorem quantum_step_inverse (D2 σ : ℝ) (d : ℕ) (hD2 : 0 < D2) (hd : 0 < d)
    (hσ : 0 < σ) :
    quantumDerivativeError (quantumStep D2 σ d) D2 d = σ := by
  have hsr : Real.sqrt (d : ℝ) ≠ 0 := by positivity
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  have h23 : 2 * Real.sqrt 3 ≠ 0 := by positivity
  unfold quantumDerivativeError quantumStep
  field_simp

theorem classical_step_inverse (D3 σ : ℝ) (hD3 : 0 < D3) (hσ : 0 < σ) :
    classicalTruncationError D3 (classicalStep D3 σ) = σ := by
  have hx : 0 ≤ 24 * σ / D3 := div_nonneg (by positivity) hD3.le
  unfold classicalTruncationError classicalStep
  rw [Real.sq_sqrt hx]
  field_simp

theorem quantumStep_pos (D2 σ : ℝ) (d : ℕ) (hD2 : 0 < D2) (hd : 0 < d)
    (hσ : 0 < σ) : 0 < quantumStep D2 σ d := by
  unfold quantumStep
  positivity

theorem classicalStep_pos (D3 σ : ℝ) (hD3 : 0 < D3) (hσ : 0 < σ) :
    0 < classicalStep D3 σ := by
  unfold classicalStep
  apply Real.sqrt_pos.mpr
  positivity

theorem both_step_inverses (D2 D3 σ : ℝ) (d : ℕ) (hD2 : 0 < D2) (hD3 : 0 < D3)
    (hd : 0 < d) (hσ : 0 < σ) :
    quantumDerivativeError (quantumStep D2 σ d) D2 d = σ
      ∧ classicalTruncationError D3 (classicalStep D3 σ) = σ :=
  ⟨quantum_step_inverse D2 σ d hD2 hd hσ, classical_step_inverse D3 σ hD3 hσ⟩

end Qatlib.Concepts.GradientOracle.StepSizes
