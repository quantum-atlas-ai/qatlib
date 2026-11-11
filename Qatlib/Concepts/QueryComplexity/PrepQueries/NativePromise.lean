/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.PrepQueries.NativeOracle

/-!
# Preparation states and overlap promises

Defines the basis input `baseState` and the rotated output `preparedState` for the native
preparation oracle. The module identifies the reverse oracle with the adjoint, proves
normalization in the unit parameter range, and computes the state overlap and its squared
modulus.

These explicit overlap and distance estimates support preparation-oracle comparisons in the
setting of [MontanaroPallister2016].

## Main statements

* `sourceOracle_inverse`: the inverse-flag oracle is the adjoint of the forward oracle.
* `preparedState_fidelity`: the squared overlap is `1 - eps` when `eps ≤ 1`.
* `preparedState_distance`: the state distance is at most `2 * sqrt eps` in the unit parameter
  range.

## References

* [Montanaro and Pallister, 2016][MontanaroPallister2016]
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder Matrix.Norms.L2Operator
namespace Qatlib.Concepts.QueryComplexity.PrepQueries

/-- Negating the sine coefficient of the rotation gives its conjugate transpose. -/
theorem rotation_adjoint (c s : ℝ) : rotation c (-s)=(rotation c s)ᴴ := by
  ext i j
  cases i <;> cases j <;> simp [rotation,Matrix.conjTranspose_apply]

/-- Negating the sine coefficient of the workspace oracle gives its conjugate transpose. -/
theorem oracle_adjoint {W : Type*} [DecidableEq W] (c s : ℝ) :
    oracle (W:=W) c (-s)=(oracle c s)ᴴ := by
  simp only [oracle,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,rotation_adjoint]

/-- The preparation oracle with inverse flag true is the conjugate transpose of the forward
oracle. -/
theorem sourceOracle_inverse {W : Type*} [DecidableEq W] (eps : ℝ) :
    sourceOracle (W:=W) eps true=(sourceOracle eps false)ᴴ := by
  simpa only [sourceOracle,Bool.false_eq_true,↓reduceIte] using
    oracle_adjoint (W:=W) (Real.sqrt (1-eps)) (Real.sqrt eps)

/-- The standard basis state at workspace coordinate `w` with Boolean flag false. -/
def baseState {W : Type*} [Fintype W] [DecidableEq W] (w : W) : EuclideanSpace ℂ (W×Bool) :=
  PiLp.single 2 (w,false) 1

/-- The base state has Euclidean norm one. -/
theorem baseState_norm {W : Type*} [Fintype W] [DecidableEq W] (w : W) : ‖baseState w‖=1 := by
  simp [baseState]

/-- The state obtained by applying the forward preparation oracle to `baseState w`. -/
def preparedState {W : Type*} [Fintype W] [DecidableEq W] (eps : ℝ) (w : W) :
    EuclideanSpace ℂ (W×Bool) :=
  Matrix.toEuclideanCLM (n:=W×Bool) (𝕜:=ℂ) (sourceOracle eps false) (baseState w)

/-- The prepared state has norm one when `0 ≤ eps ≤ 1`. -/
theorem preparedState_norm {W : Type*} [Fintype W] [DecidableEq W]
    (eps : ℝ) (he0 : 0≤eps) (he1 : eps≤1) (w : W) : ‖preparedState eps w‖=1 := by
  rw [preparedState,native_norm_map _ (sourceOracle_unitary eps he0 he1 false),baseState_norm]

/-- The overlap of the base state with the prepared state is `sqrt (1 - eps)`. -/
theorem preparedState_overlap {W : Type*} [Fintype W] [DecidableEq W] (eps : ℝ) (w : W) :
    inner ℂ (baseState w) (preparedState eps w)=(Real.sqrt (1-eps):ℂ) := by
  rw [baseState,EuclideanSpace.inner_single_left]
  simp [preparedState,baseState,sourceOracle,oracle,rotation,Matrix.mulVec,dotProduct]

/-- For `eps ≤ 1`, the squared modulus of the base-prepared overlap is `1 - eps`. -/
theorem preparedState_fidelity {W : Type*} [Fintype W] [DecidableEq W]
    (eps : ℝ) (he1 : eps≤1) (w : W) :
    Complex.normSq (inner ℂ (baseState w) (preparedState eps w))=1-eps := by
  rw [preparedState_overlap,Complex.normSq_ofReal]
  nlinarith [Real.sq_sqrt (by linarith : 0≤1-eps)]

/-- For `0 ≤ eps ≤ 1`, the base and prepared states are within Euclidean distance `2 * sqrt
eps`. -/
theorem preparedState_distance {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (eps : ℝ) (he0 : 0≤eps) (he1 : eps≤1) (w : W) :
    ‖baseState w-preparedState eps w‖≤2*Real.sqrt eps := by
  have hd : baseState w-preparedState eps w =
      Matrix.toEuclideanCLM (n:=W×Bool) (𝕜:=ℂ) (1-sourceOracle eps false) (baseState w) := by
    rw [map_sub,map_one,ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply]
    rfl
  rw [hd]
  calc
    _ ≤ ‖Matrix.toEuclideanCLM (n:=W×Bool) (𝕜:=ℂ) (1-sourceOracle eps false)‖*‖baseState w‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖(1:Matrix (W×Bool) (W×Bool) ℂ)-sourceOracle eps false‖ := by
      rw [Matrix.l2_opNorm_toEuclideanCLM,baseState_norm,mul_one]
    _ ≤ 2*Real.sqrt eps := sourceOracle_distance eps he0 he1 false

end Qatlib.Concepts.QueryComplexity.PrepQueries
