/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.CharZero.Defs
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
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.StarAlgHom
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
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Order.RelClasses
public import Mathlib.Tactic
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

/-!
# Coordinate event projections and Born weights

Defines the coordinate event projector `eventProjector` and its squared-norm weight `born` on
finite complex Euclidean spaces. The weight equals the sum of squared coordinate moduli on the
event, with no normalization required for this identity.

For unit vectors, `born_difference` bounds event-weight variation by twice the state distance.
These are finite-dimensional measurement estimates in the framework of [NielsenChuang2010].

## Main statements

* `eventProjector_norm`: event projections have operator norm at most one.
* `born_eq_sum`: event weight is a coordinate sum.
* `born_difference`: event weights of unit states differ by at most twice their distance.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace Qatlib.Concepts.QueryComplexity.PrepQueries

/-- The coordinate projection onto the event `S`, represented as a continuous linear map on
Euclidean space. -/
def eventProjector {J : Type*} [Fintype J] [DecidableEq J] (S : Finset J) :
    EuclideanSpace ℂ J →L[ℂ] EuclideanSpace ℂ J :=
  Matrix.toEuclideanCLM (n:=J) (𝕜:=ℂ) (Matrix.diagonal (fun i => if i∈S then (1:ℂ) else 0))

/-- The operator norm of an event projection is at most one. -/
theorem eventProjector_norm {J : Type*} [Fintype J] [DecidableEq J] (S : Finset J) :
    ‖eventProjector S‖ ≤ 1 := by
  rw [eventProjector, Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  split_ifs <;> norm_num

/-- The unnormalized Born weight of an event, defined as the squared norm of its projected
state. -/
def born {J : Type*} [Fintype J] [DecidableEq J] (S : Finset J) (x : EuclideanSpace ℂ J) : ℝ :=
  ‖eventProjector S x‖^2

/-- The Born weight of an event equals the sum of the squared moduli of its state coordinates. -/
theorem born_eq_sum {J : Type*} [Fintype J] [DecidableEq J]
    (S : Finset J) (x : EuclideanSpace ℂ J) :
    born S x = ∑ i∈S, Complex.normSq (x i) := by
  rw [born, PiLp.norm_sq_eq_of_L2]
  simp [eventProjector, Matrix.mulVec_diagonal, Complex.sq_norm, apply_ite]

/-- Projecting onto an event does not increase the norm of a state. -/
theorem eventProjector_apply_norm {J : Type*} [Fintype J] [DecidableEq J]
    (S : Finset J) (x : EuclideanSpace ℂ J) : ‖eventProjector S x‖ ≤ ‖x‖ := by
  calc
    _ ≤ ‖eventProjector S‖*‖x‖ := (eventProjector S).le_opNorm x
    _ ≤ 1*‖x‖ := mul_le_mul_of_nonneg_right (eventProjector_norm S) (norm_nonneg x)
    _ = ‖x‖ := one_mul _

/-- For unit vectors, the absolute difference of event Born weights is at most twice their
distance. -/
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
