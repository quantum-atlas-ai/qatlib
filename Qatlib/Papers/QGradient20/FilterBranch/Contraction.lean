/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QGradient20.FilterBranch.Operator

@[expose] public section

/-!
# A uniform contraction for the normalized gradient branch

The paper's successful branch is a normalized identity plus a signed, projected
derivative action.  The existing public development proves the pointwise norm
bound for this branch.  This module packages the same statement as an actual
continuous linear operator on the finite Euclidean space, so the constant one
is uniform over every input vector.

The index type is required to be nonempty because the distinguished coordinate
is part of the filter program.  The proof uses the Euclidean norm and the
`L2Operator` matrix norm supplied by the public QGradient20 development.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

open Matrix
open Qatlib.Papers.QGradient20.FilterBranch
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.QGradient20.FilterBranch

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

/-- The successful gradient branch as a continuous linear operator on `EuclideanSpace`. -/
def successfulAction (zero : I) (M : Matrix I I ℂ) (ξ : ℝ) (ascent : Bool) :
    EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I :=
  let _hI : Nonempty I := inferInstance
  Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I) (successOperator zero M ξ ascent)

/-- The operator realizes the pointwise successful-vector construction. -/
theorem successfulAction_apply (zero : I) (M : Matrix I I ℂ) (ξ : ℝ) (ascent : Bool)
    (x : EuclideanSpace ℂ I) :
    successfulAction zero M ξ ascent x = successfulVector zero M ξ ascent x := by
  exact successOperator_action zero M ξ ascent x

/-- The normalized branch has operator norm at most one for every nonnegative parameter.

The constant `1` is chosen before the universal input bound, giving a uniform
Euclidean contraction for the whole finite-dimensional filter branch. -/
theorem successfulAction_opNorm_le_one (zero : I) (M : Matrix I I ℂ) {ξ : ℝ}
    (hξ : 0 ≤ ξ) (ascent : Bool) :
    ‖successfulAction zero M ξ ascent‖ ≤ 1 := by
  rw [successfulAction, Matrix.l2_opNorm_toEuclideanCLM]
  exact successOperator_norm zero M hξ ascent

/-- The successful branch is one-Lipschitz on the Euclidean state space. -/
theorem successfulAction_lipschitz (zero : I) (M : Matrix I I ℂ) {ξ : ℝ}
    (hξ : 0 ≤ ξ) (ascent : Bool) (x y : EuclideanSpace ℂ I) :
    ‖successfulVector zero M ξ ascent x - successfulVector zero M ξ ascent y‖ ≤ ‖x - y‖ := by
  have h := successfulAction_opNorm_le_one zero M hξ ascent
  have hxy := (successfulAction zero M ξ ascent).le_opNorm (x - y)
  have hbound : ‖successfulAction zero M ξ ascent (x - y)‖ ≤ ‖x - y‖ := by
    exact hxy.trans ((mul_le_mul_of_nonneg_right h (norm_nonneg (x - y))).trans_eq
      (one_mul _))
  simpa only [successfulAction_apply, map_sub] using hbound

end Qatlib.Papers.QGradient20.FilterBranch
