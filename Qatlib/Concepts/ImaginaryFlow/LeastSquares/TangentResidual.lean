/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Defs

/-!
# Tangent residuals and McLachlan normal equations

This module defines the real Gram matrix `metricMatrix`, the operator overlap vector
`gradientVector`, and the squared tangent-residual cost `mclachlanCost`. Coordinate variations
compute the cost derivatives directly.

Residual orthogonality characterizes coordinate stationarity. When tangent vectors are
orthogonal to the current state, stationarity of the centered evolution residual yields the Gram
parameter-update equations used in variational imaginary-time methods [McArdleTew2020].

## Main statements

* `hasDerivAt_mclachlanCost_direction`: the coordinate derivative of the residual cost.
* `mclachlan_stationary_iff`: stationarity as tangent-residual orthogonality.
* `mclachlan_parameter_update_rule`: the componentwise Gram normal equations.

## References

* [McArdle and Tew, 2020][McArdleTew2020]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.ImaginaryFlow.LeastSquares

open scoped RealInnerProductSpace
open Finset

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The real Gram matrix of the tangent family `d`. -/
def metricMatrix {n : ℕ} (d : Fin n → E) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ⟪d i, d j⟫

/-- The vector of real inner products between the tangent vectors `d i` and `H φ`. -/
def gradientVector {n : ℕ} (d : Fin n → E) (H : E →ₗ[ℝ] E) (φ : E) : Fin n → ℝ :=
  fun i => ⟪d i, H φ⟫

/-- The squared norm of the residual formed by the real tangent combination `∑ i, v i • d i`
plus `w`. -/
def mclachlanCost {n : ℕ} (d : Fin n → E) (w : E) (v : Fin n → ℝ) : ℝ :=
  ‖(∑ i, v i • d i) + w‖ ^ 2

/-- The rate vector obtained by adding `t` only to coordinate `k`. -/
def varyRate {n : ℕ} (v : Fin n → ℝ) (k : Fin n) (t : ℝ) : Fin n → ℝ :=
  fun i => v i + if i = k then t else 0

/-- Varying one rate coordinate adds `t • d k` to the residual before taking its squared norm. -/
lemma mclachlanCost_vary {n : ℕ} (d : Fin n → E) (w : E) (v : Fin n → ℝ)
    (k : Fin n) (t : ℝ) :
    mclachlanCost d w (varyRate v k t) =
      ‖((∑ i, v i • d i) + w) + t • d k‖ ^ 2 := by
  unfold mclachlanCost
  have hsingle : (∑ i : Fin n, (if i = k then t else 0) • d i) = t • d k := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro i _ hi
      simp [hi]
    · intro hk
      simp at hk
  have hsum : (∑ i : Fin n, varyRate v k t i • d i)
      = (∑ i : Fin n, v i • d i) + t • d k := by
    have h : ∀ i : Fin n, varyRate v k t i • d i
        = v i • d i + (if i = k then t else 0) • d i := by
      intro i
      unfold varyRate
      exact add_smul _ _ _
    calc (∑ i : Fin n, varyRate v k t i • d i)
        = ∑ i : Fin n, (v i • d i + (if i = k then t else 0) • d i) :=
          Finset.sum_congr rfl fun i _ => h i
      _ = (∑ i : Fin n, v i • d i) + ∑ i : Fin n, (if i = k then t else 0) • d i :=
          Finset.sum_add_distrib
      _ = (∑ i : Fin n, v i • d i) + t • d k := by rw [hsingle]
  rw [hsum, add_right_comm]

/-- The derivative at zero of the cost along coordinate `k` is twice the real inner product of
`d k` with the residual. -/
lemma hasDerivAt_mclachlanCost_direction {n : ℕ} (d : Fin n → E) (w : E) (v : Fin n → ℝ)
    (k : Fin n) :
    HasDerivAt (fun t : ℝ => mclachlanCost d w (varyRate v k t))
      (2 * ⟪d k, (∑ i, v i • d i) + w⟫) 0 := by
  have hinner : HasDerivAt
      (fun t : ℝ => ⟪((∑ i, v i • d i) + w) + t • d k,
        ((∑ i, v i • d i) + w) + t • d k⟫)
      (2 * ⟪d k, (∑ i, v i • d i) + w⟫) 0 := by
    have hdir : HasDerivAt (fun t : ℝ => ((∑ i, v i • d i) + w) + t • d k) (d k) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => t • d k) ((1 : ℝ) • d k) 0 :=
        (hasDerivAt_id (0 : ℝ)).smul_const (d k)
      have h2 := h1.const_add ((∑ i, v i • d i) + w)
      simpa [one_smul] using h2
    have h := HasDerivAt.inner ℝ hdir hdir
    have hv : ⟪((∑ i, v i • d i) + w) + (0 : ℝ) • d k, d k⟫ +
        ⟪d k, ((∑ i, v i • d i) + w) + (0 : ℝ) • d k⟫ =
        2 * ⟪d k, (∑ i, v i • d i) + w⟫ := by
      simp only [zero_smul, add_zero]
      rw [real_inner_comm ((∑ i, v i • d i) + w) (d k)]
      ring
    rwa [hv] at h
  have hnorm : HasDerivAt
      (fun t : ℝ => ‖((∑ i, v i • d i) + w) + t • d k‖ ^ 2)
      (2 * ⟪d k, (∑ i, v i • d i) + w⟫) 0 := by
    convert hinner using 1
    ext t
    exact (real_inner_self_eq_norm_sq _).symm
  exact hnorm.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t => (mclachlanCost_vary d w v k t))

/-- Vanishing of all coordinate cost derivatives is equivalent to orthogonality of the residual
to every tangent vector. -/
theorem mclachlan_stationary_iff {n : ℕ} (d : Fin n → E) (w : E) (v : Fin n → ℝ) :
    (∀ k, HasDerivAt (fun t : ℝ => mclachlanCost d w (varyRate v k t)) 0 0) ↔
      ∀ k, ⟪d k, (∑ i, v i • d i) + w⟫ = 0 := by
  constructor
  · intro h k
    have hu := (h k).unique (hasDerivAt_mclachlanCost_direction d w v k)
    linarith
  · intro h k
    have hd := hasDerivAt_mclachlanCost_direction d w v k
    have hzero : 2 * ⟪d k, (∑ i, v i • d i) + w⟫ = 0 := by
      rw [h k]; ring
    simpa [hzero] using hd

/-- Stationarity of the centered evolution residual and tangent orthogonality to `φ` imply the
componentwise Gram normal equations for `θdot`. -/
theorem mclachlan_parameter_update_rule {n : ℕ} (d : Fin n → E) (H : E →ₗ[ℝ] E) (φ : E)
    (θdot : Fin n → ℝ)
    (hnormal : ∀ i, ⟪d i, φ⟫ = 0)
    (hstationary : ∀ k,
      ⟪d k, (∑ i, θdot i • d i) + (H φ - (⟪φ, H φ⟫) • φ)⟫ = 0) :
    ∀ k, ∑ i, metricMatrix d k i * θdot i = - gradientVector d H φ k := by
  intro k
  have hk := hstationary k
  rw [inner_add_right, inner_sub_right, inner_smul_right, hnormal k] at hk
  simp only [mul_zero, sub_zero] at hk
  have hsum : ⟪d k, ∑ i, θdot i • d i⟫ = ∑ i, metricMatrix d k i * θdot i := by
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [inner_smul_right]
    simp [metricMatrix, mul_comm]
  rw [hsum] at hk
  simp only [metricMatrix, gradientVector] at hk ⊢
  linarith

end Qatlib.Concepts.ImaginaryFlow.LeastSquares
