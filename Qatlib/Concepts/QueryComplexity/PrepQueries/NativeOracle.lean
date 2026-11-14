/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Algebra.Star.StarRingHom
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Rat.Init
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Tactic
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

/-!
# Native preparation rotation oracles

Defines a real rotation on a Boolean register and its workspace extension `oracle`. The module
proves unitarity and an exact Gram identity for the difference from the identity, yielding an
exact squared operator-norm distance on nonempty workspaces.

`sourceOracle` specializes the rotation to preparation coefficients determined by an error
parameter and allows either rotation direction. Preparation-query costs in quantum numerical
algorithms motivate this model [MontanaroPallister2016].

## Main statements

* `oracle_distance_sq`: the squared distance from the identity is `2 * (1 - c)`.
* `sourceOracle_unitary`: preparation oracles are unitary for error parameters in the unit
  interval.
* `sourceOracle_distance`: either oracle direction is within `2 * sqrt eps` of the identity.

## References

* [Montanaro and Pallister, 2016][MontanaroPallister2016]
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker Matrix.Norms.L2Operator
namespace Qatlib.Concepts.QueryComplexity.PrepQueries

/-- The real two-dimensional rotation matrix with rows `(c, -s)` and `(s, c)` in the Boolean
basis. -/
def rotation (c s : ℝ) : Matrix Bool Bool ℂ := fun i j =>
  if i then (if j then c else s) else (if j then -s else c)

/-- The rotation matrix is unitary when `c^2 + s^2 = 1`. -/
theorem rotation_unitary (c s : ℝ) (h : c^2+s^2=1) :
    rotation c s ∈ Matrix.unitaryGroup Bool ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change (rotation c s)ᴴ * rotation c s = 1
  ext i j
  have hc : (c:ℂ)^2+(s:ℂ)^2=1 := by exact_mod_cast h
  cases i <;> cases j <;>
    simp [rotation, Matrix.mul_apply, Matrix.conjTranspose_apply] <;>
    ring_nf
  all_goals linear_combination hc

/-- For a unitary rotation, the Gram matrix of its difference from the identity is `2 * (1 - c)`
times the identity. -/
theorem rotation_difference_gram (c s : ℝ) (h : c^2+s^2=1) :
    (1-rotation c s)ᴴ * (1-rotation c s) = (2*(1-c):ℂ) • (1:Matrix Bool Bool ℂ) := by
  ext i j
  have hc : (c:ℂ)^2+(s:ℂ)^2=1 := by exact_mod_cast h
  cases i <;> cases j <;>
    simp [rotation, Matrix.mul_apply, Matrix.conjTranspose_apply] <;>
    ring_nf
  all_goals linear_combination hc

/-- The rotation oracle acting on a Boolean register and identically on the workspace. -/
def oracle {W : Type*} [DecidableEq W] (c s : ℝ) : Matrix (W×Bool) (W×Bool) ℂ :=
  (1:Matrix W W ℂ) ⊗ₖ rotation c s

/-- The workspace rotation oracle is unitary when its coefficients satisfy `c^2 + s^2 = 1`. -/
theorem oracle_unitary {W : Type*} [Fintype W] [DecidableEq W]
    (c s : ℝ) (h : c^2+s^2=1) : oracle (W:=W) c s ∈ Matrix.unitaryGroup (W×Bool) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change ((1:Matrix W W ℂ) ⊗ₖ rotation c s)ᴴ * (1 ⊗ₖ rotation c s) = 1
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
  have hr := Matrix.mem_unitaryGroup_iff'.mp (rotation_unitary c s h)
  change (rotation c s)ᴴ * rotation c s = 1 at hr
  rw [hr]
  simp

/-- The Gram matrix of the identity minus the workspace oracle is `2 * (1 - c)` times the
identity. -/
theorem oracle_difference_gram {W : Type*} [Fintype W] [DecidableEq W]
    (c s : ℝ) (h : c^2+s^2=1) :
    (1-oracle (W:=W) c s)ᴴ * (1-oracle (W:=W) c s) =
      (2*(1-c):ℂ) • (1:Matrix (W×Bool) (W×Bool) ℂ) := by
  have hd : (1:Matrix (W×Bool) (W×Bool) ℂ)-oracle c s =
      (1:Matrix W W ℂ) ⊗ₖ (1-rotation c s) := by
    ext ⟨w,i⟩ ⟨v,j⟩
    by_cases hw : w=v <;> simp [oracle, Matrix.one_apply, hw, mul_sub]
  rw [hd, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    rotation_difference_gram c s h]
  simp [Matrix.kronecker_smul]

/-- On a nonempty workspace, the squared operator-norm distance from the rotation oracle to the
identity is `2 * (1 - c)`. -/
theorem oracle_distance_sq {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (c s : ℝ) (h : c^2+s^2=1) (hc : c≤1) :
    ‖(1:Matrix (W×Bool) (W×Bool) ℂ)-oracle c s‖^2 = 2*(1-c) := by
  rw [pow_two, ← Matrix.l2_opNorm_conjTranspose_mul_self, oracle_difference_gram c s h,
    norm_smul, norm_one, mul_one]
  rw [show (2*(1-c):ℂ) = ((2*(1-c):ℝ):ℂ) by push_cast; rfl]
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (by linarith)

/-- A unitary matrix preserves the Euclidean norm under its associated continuous linear map. -/
theorem native_norm_map {J : Type*} [Fintype J] [DecidableEq J]
    (A : Matrix J J ℂ) (hA : A∈Matrix.unitaryGroup J ℂ) (x : EuclideanSpace ℂ J) :
    ‖Matrix.toEuclideanCLM (n:=J) (𝕜:=ℂ) A x‖ = ‖x‖ := by
  apply ContinuousLinearMap.norm_map_of_mem_unitary
  apply Unitary.mem_iff.mpr
  constructor
  · simpa only [← map_star, ← map_mul, map_one] using
      congrArg (Matrix.toEuclideanCLM (n:=J) (𝕜:=ℂ)) (Unitary.star_mul_self_of_mem hA)
  · simpa only [← map_star, ← map_mul, map_one] using
      congrArg (Matrix.toEuclideanCLM (n:=J) (𝕜:=ℂ)) (Unitary.mul_star_self_of_mem hA)

/-- The preparation oracle with coefficients `sqrt (1 - eps)` and signed `sqrt eps`, with the
inverse flag choosing the negative sign. -/
def sourceOracle {W : Type*} [DecidableEq W] (eps : ℝ) (inverse : Bool) :
    Matrix (W×Bool) (W×Bool) ℂ :=
  oracle (Real.sqrt (1-eps)) (if inverse then -Real.sqrt eps else Real.sqrt eps)

/-- For `0 ≤ eps ≤ 1`, the preparation coefficients satisfy the rotation normalization identity
for either sign. -/
theorem source_coefficients (eps : ℝ) (he0 : 0≤eps) (he1 : eps≤1) (b : Bool) :
    Real.sqrt (1-eps)^2+(if b then -Real.sqrt eps else Real.sqrt eps)^2=1 := by
  have hc := Real.sq_sqrt (by linarith : 0≤1-eps)
  have hs := Real.sq_sqrt he0
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, neg_sq] <;> linarith

/-- The preparation oracle is unitary for `0 ≤ eps ≤ 1` and either inverse flag. -/
theorem sourceOracle_unitary {W : Type*} [Fintype W] [DecidableEq W]
    (eps : ℝ) (he0 : 0≤eps) (he1 : eps≤1) (b : Bool) :
    sourceOracle (W:=W) eps b ∈ Matrix.unitaryGroup (W×Bool) ℂ :=
  oracle_unitary _ _ (source_coefficients eps he0 he1 b)

/-- For `0 ≤ eps ≤ 1` on a nonempty workspace, the preparation oracle is within operator-norm
distance `2 * sqrt eps` of the identity. -/
theorem sourceOracle_distance {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (eps : ℝ) (he0 : 0≤eps) (he1 : eps≤1) (b : Bool) :
    ‖(1:Matrix (W×Bool) (W×Bool) ℂ)-sourceOracle eps b‖ ≤ 2*Real.sqrt eps := by
  have hc := Real.sq_sqrt (by linarith : 0≤1-eps)
  have hs := Real.sq_sqrt he0
  have hc0 := Real.sqrt_nonneg (1-eps)
  have hc1 : Real.sqrt (1-eps) ≤ 1 := by nlinarith
  have hsq := oracle_distance_sq (W:=W) (Real.sqrt (1-eps))
    (if b then -Real.sqrt eps else Real.sqrt eps) (source_coefficients eps he0 he1 b) hc1
  change ‖(1:Matrix (W×Bool) (W×Bool) ℂ)-sourceOracle eps b‖^2 = _ at hsq
  have hn := norm_nonneg ((1:Matrix (W×Bool) (W×Bool) ℂ)-sourceOracle eps b)
  have hs0 := Real.sqrt_nonneg eps
  nlinarith

end Qatlib.Concepts.QueryComplexity.PrepQueries
