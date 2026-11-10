/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.RelClasses
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Defs

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PartitionFunc08.MainResults.ApproxReflection

open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem norm_pow_le_one (R : E →L[ℂ] E) (hR : ‖R‖ ≤ 1) (k : ℕ) : ‖R ^ k‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [pow_zero, ContinuousLinearMap.one_def]
    exact ContinuousLinearMap.norm_id_le (𝕜 := ℂ)
  · calc ‖R ^ k‖ ≤ ‖R‖ ^ k := norm_pow_le' _ hk
      _ ≤ 1 := pow_le_one₀ (norm_nonneg _) hR

theorem approx_reflection_error_accumulation (R Rt : E →L[ℂ] E) {εR : ℝ} (hεR : 0 ≤ εR)
    (hRt : ‖Rt‖ ≤ 1) (hR : ‖R‖ ≤ 1) (hdiff : ‖Rt - R‖ ≤ εR) (k : ℕ) :
    ‖Rt ^ k - R ^ k‖ ≤ k * εR := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsplit : Rt ^ (k + 1) - R ^ (k + 1) =
        Rt ^ k * (Rt - R) + (Rt ^ k - R ^ k) * R := by
      rw [pow_succ, pow_succ]
      noncomm_ring
    have hRt_pow : ‖Rt ^ k‖ ≤ 1 := norm_pow_le_one Rt hRt k
    have hnorm : ‖Rt ^ k * (Rt - R) + (Rt ^ k - R ^ k) * R‖ ≤
        ‖Rt ^ k‖ * ‖Rt - R‖ + ‖Rt ^ k - R ^ k‖ * ‖R‖ :=
      (norm_add_le _ _).trans
        (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    rw [hsplit]
    calc ‖Rt ^ k * (Rt - R) + (Rt ^ k - R ^ k) * R‖
        ≤ ‖Rt ^ k‖ * ‖Rt - R‖ + ‖Rt ^ k - R ^ k‖ * ‖R‖ := hnorm
      _ ≤ 1 * εR + (k * εR) * 1 := by
          have h1 : ‖Rt ^ k‖ * ‖Rt - R‖ ≤ 1 * εR :=
            mul_le_mul hRt_pow hdiff (norm_nonneg _) (by norm_num)
          have h2 : ‖Rt ^ k - R ^ k‖ * ‖R‖ ≤ (k * εR) * 1 :=
            mul_le_mul ih hR (norm_nonneg _) (mul_nonneg (by positivity) hεR)
          linarith
      _ = (↑(k + 1) : ℝ) * εR := by
          rw [Nat.cast_add, Nat.cast_one]
          ring

theorem approx_reflection_budget (R Rt : E →L[ℂ] E) {εR : ℝ} (hεR : 0 ≤ εR)
    (hRt : ‖Rt‖ ≤ 1) (hR : ‖R‖ ≤ 1) (hdiff : ‖Rt - R‖ ≤ εR) (k : ℕ)
    (hbudget : (k : ℝ) * εR ≤ 1 / 32) :
    ‖Rt ^ k - R ^ k‖ ≤ 1 / 32 :=
  (approx_reflection_error_accumulation R Rt hεR hRt hR hdiff k).trans hbudget

theorem lemma5_approx_reflection (R Rt : E →L[ℂ] E) {εR : ℝ} (hεR : 0 ≤ εR)
    (hRt : ‖Rt‖ ≤ 1) (hR : ‖R‖ ≤ 1) (hdiff : ‖Rt - R‖ ≤ εR) (k : ℕ)
    (hbudget : (k : ℝ) * εR ≤ 1 / 32) :
    ‖Rt ^ k - R ^ k‖ ≤ 1 / 32 :=
  approx_reflection_budget R Rt hεR hRt hR hdiff k hbudget

end Qatlib.Papers.PartitionFunc08.MainResults.ApproxReflection
