/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ProjectorQAOA26.StageStability.PhaseDist
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Euclidean vector norms and matrix operator norms

This module relates the explicit finite-vector norm `l2norm` to the norm on `EuclideanSpace`.
The resulting action bounds connect vector estimates to the matrix operator norms used in the
stability analysis of [ZhouAnLiu2026].

## Main statements

* `l2norm_mulVec_le`: The Euclidean norm of a matrix-vector product is at most the matrix
  operator norm times the vector norm.
* `opNorm_le_of_l2`: A nonnegative uniform bound on matrix action in `l2norm` bounds the matrix
  operator norm.

## References

* [Zhou et al., 2026][ZhouAnLiu2026]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.ProjectorQAOA26.StageStability

open scoped BigOperators Matrix Matrix.Norms.L2Operator

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in

/-- Converting a complex coordinate vector to `EuclideanSpace` preserves its explicit Euclidean
norm `l2norm`. -/
theorem norm_toLp (y : I → ℂ) : ‖(WithLp.toLp 2 y : EuclideanSpace ℂ I)‖ = l2norm y := by
  rw [EuclideanSpace.norm_eq, l2norm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => (Complex.normSq_eq_norm_sq (y i)).symm

omit [DecidableEq I] in

/-- The norm of a vector in `EuclideanSpace` equals `l2norm` of its underlying coordinate
function. -/
theorem norm_ofLp (z : EuclideanSpace ℂ I) : ‖z‖ = l2norm (WithLp.ofLp z) := by
  have hz : z = WithLp.toLp 2 (WithLp.ofLp z) := rfl
  rw [hz, norm_toLp]

/-- The Euclidean norm of a matrix-vector product is at most the matrix operator norm times the
vector norm. -/
theorem l2norm_mulVec_le (A : Matrix I I ℂ) (x : I → ℂ) :
    l2norm (A *ᵥ x) ≤ ‖A‖ * l2norm x := by
  have h := Matrix.l2_opNorm_mulVec (n := I) (m := I) (𝕜 := ℂ) A (WithLp.toLp 2 x)
  have h2 : (EuclideanSpace.equiv I ℂ).symm (A *ᵥ WithLp.toLp 2 x)
      = WithLp.toLp 2 (A *ᵥ x) := rfl
  rw [h2, norm_toLp, norm_toLp] at h
  exact h

/-- A nonnegative uniform bound on matrix action in `l2norm` bounds the matrix operator norm. -/
theorem opNorm_le_of_l2 {A : Matrix I I ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ x : I → ℂ, l2norm (A *ᵥ x) ≤ r * l2norm x) : ‖A‖ ≤ r := by
  set T := Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) A with hT
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  refine T.opNorm_le_bound hr ?_
  intro x
  have h1 := h (WithLp.ofLp x)
  have e1 : WithLp.ofLp (T x) = A *ᵥ WithLp.ofLp x := by
    rw [hT]
    exact Matrix.ofLp_toEuclideanCLM A x
  calc ‖T x‖ = l2norm (WithLp.ofLp (T x)) := norm_ofLp _
    _ = l2norm (A *ᵥ WithLp.ofLp x) := by rw [e1]
    _ ≤ r * l2norm (WithLp.ofLp x) := h1
    _ = r * ‖x‖ := by rw [norm_ofLp x]

end Qatlib.Papers.ProjectorQAOA26.StageStability
