/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Step sizes for prescribed derivative error

This module defines the classical truncation-error and quantum derivative-error models, along
with step sizes solving each model for a target tolerance. It proves positivity and exact
substitution identities for the comparison in [Jordan2005Gradient].

## Main statements

* `quantum_step_inverse`: substituting `quantumStep` returns the target error.
* `classical_step_inverse`: substituting `classicalStep` returns the target error.
* `both_step_inverses`: the two identities hold together under positive parameter assumptions.

## References

* [Jordan, 2005][Jordan2005Gradient]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.GradientOracle.StepSizes

/-- The quantum derivative-error model `l*D2*sqrt d/(2*sqrt 3)`. -/
def quantumDerivativeError (l D2 : ℝ) (d : ℕ) : ℝ :=
  l * D2 * Real.sqrt d / (2 * Real.sqrt 3)

/-- The classical centered-difference truncation-error model `D3*l^2/24`. -/
def classicalTruncationError (D3 l : ℝ) : ℝ := D3 * l ^ 2 / 24

/-- The step length `2*sqrt 3*σ/(D2*sqrt d)` selected for the quantum derivative-error model. -/
def quantumStep (D2 σ : ℝ) (d : ℕ) : ℝ :=
  2 * Real.sqrt 3 * σ / (D2 * Real.sqrt d)

/-- The step length `sqrt (24*σ/D3)` selected for the classical truncation-error model. -/
def classicalStep (D3 σ : ℝ) : ℝ := Real.sqrt (24 * σ / D3)

/-- For positive derivative bound, target error, and dimension, substituting `quantumStep` into
`quantumDerivativeError` gives exactly `σ`. See [Jordan2005Gradient]. -/
theorem quantum_step_inverse (D2 σ : ℝ) (d : ℕ) (hD2 : 0 < D2) (hd : 0 < d)
    (hσ : 0 < σ) :
    quantumDerivativeError (quantumStep D2 σ d) D2 d = σ := by
  have hsr : Real.sqrt (d : ℝ) ≠ 0 := by positivity
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  have h23 : 2 * Real.sqrt 3 ≠ 0 := by positivity
  unfold quantumDerivativeError quantumStep
  field_simp

/-- For positive third-derivative bound and target error, substituting `classicalStep` into
`classicalTruncationError` gives exactly `σ`. See [Jordan2005Gradient]. -/
theorem classical_step_inverse (D3 σ : ℝ) (hD3 : 0 < D3) (hσ : 0 < σ) :
    classicalTruncationError D3 (classicalStep D3 σ) = σ := by
  have hx : 0 ≤ 24 * σ / D3 := div_nonneg (by positivity) hD3.le
  unfold classicalTruncationError classicalStep
  rw [Real.sq_sqrt hx]
  field_simp

/-- The selected quantum step is positive when the derivative bound, target error, and dimension
are positive. -/
theorem quantumStep_pos (D2 σ : ℝ) (d : ℕ) (hD2 : 0 < D2) (hd : 0 < d)
    (hσ : 0 < σ) : 0 < quantumStep D2 σ d := by
  unfold quantumStep
  positivity

/-- The selected classical step is positive when the third-derivative bound and target error are
positive. -/
theorem classicalStep_pos (D3 σ : ℝ) (hD3 : 0 < D3) (hσ : 0 < σ) :
    0 < classicalStep D3 σ := by
  unfold classicalStep
  apply Real.sqrt_pos.mpr
  positivity

/-- For positive derivative bounds, target error, and dimension, both selected step lengths
yield exactly `σ` in their respective error models. See [Jordan2005Gradient]. -/
theorem both_step_inverses (D2 D3 σ : ℝ) (d : ℕ) (hD2 : 0 < D2) (hD3 : 0 < D3)
    (hd : 0 < d) (hσ : 0 < σ) :
    quantumDerivativeError (quantumStep D2 σ d) D2 d = σ
      ∧ classicalTruncationError D3 (classicalStep D3 σ) = σ :=
  ⟨quantum_step_inverse D2 σ d hD2 hd hσ, classical_step_inverse D3 σ hD3 hσ⟩

end Qatlib.Concepts.GradientOracle.StepSizes
