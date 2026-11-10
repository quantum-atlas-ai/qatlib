/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Action.Pi
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarRingHom
import Mathlib.Algebra.Star.Unitary
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Rat.Init
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.LinearCombination.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.UniformMulAction
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Defs
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker Matrix.Norms.L2Operator
namespace Qatlib.Concepts.QueryComplexity.PrepQueries

def rotation (c s : ℝ) : Matrix Bool Bool ℂ := fun i j =>
  if i then (if j then c else s) else (if j then -s else c)

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

theorem rotation_difference_gram (c s : ℝ) (h : c^2+s^2=1) :
    (1-rotation c s)ᴴ * (1-rotation c s) = (2*(1-c):ℂ) • (1:Matrix Bool Bool ℂ) := by
  ext i j
  have hc : (c:ℂ)^2+(s:ℂ)^2=1 := by exact_mod_cast h
  cases i <;> cases j <;>
    simp [rotation, Matrix.mul_apply, Matrix.conjTranspose_apply] <;>
    ring_nf
  all_goals linear_combination hc

def oracle {W : Type*} [DecidableEq W] (c s : ℝ) : Matrix (W×Bool) (W×Bool) ℂ :=
  (1:Matrix W W ℂ) ⊗ₖ rotation c s

theorem oracle_unitary {W : Type*} [Fintype W] [DecidableEq W]
    (c s : ℝ) (h : c^2+s^2=1) : oracle (W:=W) c s ∈ Matrix.unitaryGroup (W×Bool) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change ((1:Matrix W W ℂ) ⊗ₖ rotation c s)ᴴ * (1 ⊗ₖ rotation c s) = 1
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
  have hr := Matrix.mem_unitaryGroup_iff'.mp (rotation_unitary c s h)
  change (rotation c s)ᴴ * rotation c s = 1 at hr
  rw [hr]
  simp

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

theorem oracle_distance_sq {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (c s : ℝ) (h : c^2+s^2=1) (hc : c≤1) :
    ‖(1:Matrix (W×Bool) (W×Bool) ℂ)-oracle c s‖^2 = 2*(1-c) := by
  rw [pow_two, ← Matrix.l2_opNorm_conjTranspose_mul_self, oracle_difference_gram c s h,
    norm_smul, norm_one, mul_one]
  rw [show (2*(1-c):ℂ) = ((2*(1-c):ℝ):ℂ) by push_cast; rfl]
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (by linarith)

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

def sourceOracle {W : Type*} [DecidableEq W] (eps : ℝ) (inverse : Bool) :
    Matrix (W×Bool) (W×Bool) ℂ :=
  oracle (Real.sqrt (1-eps)) (if inverse then -Real.sqrt eps else Real.sqrt eps)

theorem source_coefficients (eps : ℝ) (he0 : 0≤eps) (he1 : eps≤1) (b : Bool) :
    Real.sqrt (1-eps)^2+(if b then -Real.sqrt eps else Real.sqrt eps)^2=1 := by
  have hc := Real.sq_sqrt (by linarith : 0≤1-eps)
  have hs := Real.sq_sqrt he0
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, neg_sq] <;> linarith

theorem sourceOracle_unitary {W : Type*} [Fintype W] [DecidableEq W]
    (eps : ℝ) (he0 : 0≤eps) (he1 : eps≤1) (b : Bool) :
    sourceOracle (W:=W) eps b ∈ Matrix.unitaryGroup (W×Bool) ℂ :=
  oracle_unitary _ _ (source_coefficients eps he0 he1 b)

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
