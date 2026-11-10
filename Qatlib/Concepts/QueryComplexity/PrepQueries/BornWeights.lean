/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.CharZero.Defs
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
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Action.Pi
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.StarAlgHom
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
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Order.RelClasses
import Mathlib.Tactic
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.UniformMulAction
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.Defs
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace Qatlib.Concepts.QueryComplexity.PrepQueries

def eventProjector {J : Type*} [Fintype J] [DecidableEq J] (S : Finset J) :
    EuclideanSpace ℂ J →L[ℂ] EuclideanSpace ℂ J :=
  Matrix.toEuclideanCLM (n:=J) (𝕜:=ℂ) (Matrix.diagonal (fun i => if i∈S then (1:ℂ) else 0))

theorem eventProjector_norm {J : Type*} [Fintype J] [DecidableEq J] (S : Finset J) :
    ‖eventProjector S‖ ≤ 1 := by
  rw [eventProjector, Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  split_ifs <;> norm_num

def born {J : Type*} [Fintype J] [DecidableEq J] (S : Finset J) (x : EuclideanSpace ℂ J) : ℝ :=
  ‖eventProjector S x‖^2

theorem born_eq_sum {J : Type*} [Fintype J] [DecidableEq J]
    (S : Finset J) (x : EuclideanSpace ℂ J) :
    born S x = ∑ i∈S, Complex.normSq (x i) := by
  rw [born, PiLp.norm_sq_eq_of_L2]
  simp [eventProjector, Matrix.mulVec_diagonal, Complex.sq_norm, apply_ite]

theorem eventProjector_apply_norm {J : Type*} [Fintype J] [DecidableEq J]
    (S : Finset J) (x : EuclideanSpace ℂ J) : ‖eventProjector S x‖ ≤ ‖x‖ := by
  calc
    _ ≤ ‖eventProjector S‖*‖x‖ := (eventProjector S).le_opNorm x
    _ ≤ 1*‖x‖ := mul_le_mul_of_nonneg_right (eventProjector_norm S) (norm_nonneg x)
    _ = ‖x‖ := one_mul _

theorem born_difference {J : Type*} [Fintype J] [DecidableEq J]
    (S : Finset J) (x y : EuclideanSpace ℂ J) (hx : ‖x‖=1) (hy : ‖y‖=1) :
    |born S x-born S y| ≤ 2*‖x-y‖ := by
  have hp := eventProjector_apply_norm S x
  have hq := eventProjector_apply_norm S y
  have hd : |‖eventProjector S x‖-‖eventProjector S y‖| ≤ ‖x-y‖ := by
    calc
      _ ≤ ‖eventProjector S x-eventProjector S y‖ := abs_norm_sub_norm_le _ _
      _ = ‖eventProjector S (x-y)‖ := by rw [map_sub]
      _ ≤ ‖x-y‖ := eventProjector_apply_norm S (x-y)
  have hp0 := norm_nonneg (eventProjector S x)
  have hq0 := norm_nonneg (eventProjector S y)
  have hsum : ‖eventProjector S x‖+‖eventProjector S y‖ ≤ 2 := by
    rw [hx] at hp;rw [hy] at hq;linarith
  unfold born
  rw [show ‖eventProjector S x‖^2-‖eventProjector S y‖^2 =
    (‖eventProjector S x‖-‖eventProjector S y‖)*(‖eventProjector S x‖+‖eventProjector S y‖) by ring,
    abs_mul, abs_of_nonneg (add_nonneg hp0 hq0)]
  calc
    _ ≤ ‖x-y‖*2 := mul_le_mul hd hsum (add_nonneg hp0 hq0) (norm_nonneg _)
    _ = 2*‖x-y‖ := mul_comm _ _
end Qatlib.Concepts.QueryComplexity.PrepQueries
