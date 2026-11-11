/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QGradient20.FilterBranch.ActualVector
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# The successful gradient-filter operator

`successOperator` represents the successful-vector map as a matrix. Its induced action equals
`successfulVector`, it is a contraction for nonnegative branch parameter, and real normalization
preserves Hermitian matrices. The mathematical context is [GaoEtAl2021].

## Main statements

* `successOperator_action`: The continuous linear action of `successOperator` on a vector equals
  `successfulVector`.
* `successOperator_norm`: For a nonnegative branch parameter, the successful operator has
  operator norm at most one.

## References

* [Gao et al., 2021][GaoEtAl2021]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.QGradient20.FilterBranch
variable {I : Type} [Fintype I] [DecidableEq I]

/-- Spectral normalization preserves Hermitian matrices. -/
theorem normalizedMatrix_hermitian (M : Matrix I I ℂ) (hM : M.IsHermitian) :
    (normalizedMatrix M).IsHermitian :=
  hM.smul (R := ℝ) (IsSelfAdjoint.all _)

/-- The matrix `(1+ξ)⁻¹ * (I + branchSign ascent * ξ * K * normalizedMatrix M)`, where `K`
removes the distinguished coordinate. -/
def successOperator (zero : I) (M : Matrix I I ℂ) (ξ : ℝ) (ascent : Bool) : Matrix I I ℂ :=
  ((1+ξ)⁻¹ : ℝ) • (1 + (branchSign ascent * ξ : ℝ) • (projectionMatrix zero * normalizedMatrix M))

/-- The continuous linear action of `successOperator` on a vector equals `successfulVector`. -/
theorem successOperator_action (zero : I) (M : Matrix I I ℂ) (ξ : ℝ) (ascent : Bool)
    (x : EuclideanSpace ℂ I) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I)) (successOperator zero M ξ ascent) x =
      successfulVector zero M ξ ascent x := by
  apply (EuclideanSpace.equiv I ℂ).injective
  funext i
  change (successOperator zero M ξ ascent *ᵥ x.ofLp) i = _
  simp only [successOperator, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec, successfulVector, update, project, derivativeAction]
  rfl

/-- For a nonnegative branch parameter, the successful operator has operator norm at most one. -/
theorem successOperator_norm (zero : I) (M : Matrix I I ℂ) {ξ : ℝ} (hξ : 0 ≤ ξ) (ascent : Bool) :
    ‖successOperator zero M ξ ascent‖ ≤ 1 := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  rw [successOperator_action]
  simpa only [one_mul] using successfulVector_norm_le zero M hξ ascent x

end Qatlib.Papers.QGradient20.FilterBranch
