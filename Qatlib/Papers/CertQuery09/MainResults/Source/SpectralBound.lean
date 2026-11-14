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
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Analysis.CStarAlgebra.Matrix
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
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Nonempty
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Tactic
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

/-!
# Operator norms from nonnegative row sums

This module bounds the Euclidean operator norm of a finite symmetric nonnegative real matrix by
a uniform row-sum bound. On a nonempty index type, a constant row sum also gives a lower bound
and hence an exact norm formula, supporting the adversary matrices used for [AmbainisEtAl2009].

## Main statements

* `l2_opNorm_le_of_row_sum_le`: gives the row-sum upper bound.
* `l2_opNorm_eq_of_regular`: computes the norm of a symmetric nonnegative matrix with constant
  row sum.

## References

* [Ambainis et al., 2009][AmbainisEtAl2009]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.CertQuery09.MainResults.Source

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A symmetric entrywise nonnegative real matrix whose row sums are bounded by `r ≥ 0` has
Euclidean operator norm at most `r`. -/
theorem l2_opNorm_le_of_row_sum_le (A : Matrix ι ι ℝ)
    (h0 : ∀ x y, 0 ≤ A x y) (hsym : ∀ x y, A x y = A y x)
    {r : ℝ} (hr : 0 ≤ r) (hrow : ∀ x, ∑ y, A x y ≤ r) :
    ‖A‖ ≤ r := by
  rw [← l2_opNorm_toEuclideanCLM (A := A)]
  refine ContinuousLinearMap.opNorm_le_bound _ hr fun x => ?_
  have hTx : ‖toEuclideanCLM (n := ι) (𝕜 := ℝ) A x‖ ^ 2
      = ∑ i, (∑ j, A i j * x j) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    have happ : toEuclideanCLM (n := ι) (𝕜 := ℝ) A x i = ∑ j, A i j * x j := by
      have h := congrFun (ofLp_toEuclideanCLM A x) i
      simp only [mulVec, dotProduct] at h
      exact h
    rw [happ]
  have hsq : ‖toEuclideanCLM (n := ι) (𝕜 := ℝ) A x‖ ^ 2 ≤ (r * ‖x‖) ^ 2 := by
    rw [hTx, mul_pow, show ‖x‖ ^ 2 = ∑ j, x j ^ 2 from EuclideanSpace.real_norm_sq_eq x,
      Finset.mul_sum]
    calc ∑ i, (∑ j, A i j * x j) ^ 2
        ≤ ∑ i, (∑ j, A i j) * (∑ j, A i j * x j ^ 2) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ)
            (r := fun j => A i j * x j) (f := fun j => A i j)
            (g := fun j => A i j * x j ^ 2)
            (fun j _ => h0 i j)
            (fun j _ => mul_nonneg (h0 i j) (sq_nonneg _))
            (fun j _ => le_of_eq (by ring))
          simpa only using hcs
      _ ≤ ∑ i, r * (∑ j, A i j * x j ^ 2) := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact mul_le_mul_of_nonneg_right (hrow i)
            (Finset.sum_nonneg fun j _ => mul_nonneg (h0 i j) (sq_nonneg _))
      _ = r * ∑ i, ∑ j, A i j * x j ^ 2 := by
          rw [Finset.mul_sum]
      _ = r * ∑ j, (∑ i, A i j) * x j ^ 2 := by
          congr 1
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_mul]
      _ ≤ r * ∑ j, r * x j ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ hr
          refine Finset.sum_le_sum fun j _ => ?_
          have hcol : ∑ i, A i j ≤ r := by
            rw [Finset.sum_congr rfl fun i _ => hsym i j]
            exact hrow j
          exact mul_le_mul_of_nonneg_right hcol (sq_nonneg _)
      _ = ∑ j, r ^ 2 * x j ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hr (norm_nonneg _))).mp hsq

variable [Nonempty ι]

/-- On a nonempty finite index type, an entrywise nonnegative real matrix with constant row sum
`r` has Euclidean operator norm at least `r`. -/
theorem row_sum_eq_le_l2_opNorm (A : Matrix ι ι ℝ)
    (h0 : ∀ x y, 0 ≤ A x y) {r : ℝ} (hrow : ∀ x, ∑ y, A x y = r) :
    r ≤ ‖A‖ := by
  have hr : 0 ≤ r := by
    rw [← hrow (Classical.arbitrary ι)]
    exact Finset.sum_nonneg fun j _ => h0 _ j
  set ones : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun _ : ι => (1 : ℝ)) with hones
  have honesq : 0 < ‖ones‖ := by
    have h2 : ‖ones‖ ^ 2 = (Fintype.card ι : ℝ) := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [hones]
    have hc : (0 : ℝ) < (Fintype.card ι : ℝ) := by
      exact_mod_cast Fintype.card_pos
    nlinarith [norm_nonneg ones]
  have hAx : toEuclideanCLM (n := ι) (𝕜 := ℝ) A ones = r • ones := by
    rw [hones]
    apply_fun WithLp.ofLp
    case inj => exact WithLp.ofLp_injective 2
    funext i
    simp only [ofLp_toEuclideanCLM, WithLp.ofLp_smul, mulVec, dotProduct,
      Pi.smul_apply, smul_eq_mul, mul_one, hrow i]
  have hnorm : ‖toEuclideanCLM (n := ι) (𝕜 := ℝ) A ones‖ = r * ‖ones‖ := by
    rw [hAx, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
  have hratio := ContinuousLinearMap.ratio_le_opNorm (toEuclideanCLM (n := ι) (𝕜 := ℝ) A) ones
  rw [hnorm, mul_div_cancel_right₀ r (ne_of_gt honesq)] at hratio
  simpa using! hratio

/-- On a nonempty finite index type, a symmetric entrywise nonnegative real matrix with constant
row sum `r` has Euclidean operator norm exactly `r`. -/
theorem l2_opNorm_eq_of_regular (A : Matrix ι ι ℝ)
    (h0 : ∀ x y, 0 ≤ A x y) (hsym : ∀ x y, A x y = A y x)
    {r : ℝ} (hrow : ∀ x, ∑ y, A x y = r) :
    ‖A‖ = r := by
  have hr : 0 ≤ r := by
    rw [← hrow (Classical.arbitrary ι)]
    exact Finset.sum_nonneg fun j _ => h0 _ j
  exact le_antisymm
    (l2_opNorm_le_of_row_sum_le A h0 hsym hr fun x => le_of_eq (hrow x))
    (row_sum_eq_le_l2_opNorm A h0 hrow)

end Qatlib.Papers.CertQuery09.MainResults.Source
