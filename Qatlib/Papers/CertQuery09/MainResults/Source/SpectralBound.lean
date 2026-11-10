/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Action.Pi
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Analysis.CStarAlgebra.Matrix
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
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.Nonempty
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.UniformMulAction
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Defs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.CertQuery09.MainResults.Source

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

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
