/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp.Lemmas

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MonteCarloInt20.CostModels.LeadingQuery

def queriesPerTermPrev (D : ℝ) : ℝ := D

def queriesPerTermNew (C δ : ℝ) : ℝ := C / δ

theorem queries_new_eq_order (C δ : ℝ) :
    queriesPerTermNew C δ = C * δ⁻¹ := by
  unfold queriesPerTermNew
  rw [div_eq_mul_inv]

theorem main_query_reduction (C δ D : ℝ) (hC : 0 < C) (hδ : 0 < δ) (hD : 0 < D) :
    queriesPerTermNew C δ / queriesPerTermPrev D = C * (δ⁻¹ / D) := by
  unfold queriesPerTermNew queriesPerTermPrev
  have hδ' : δ ≠ 0 := ne_of_gt hδ
  have hD' : D ≠ 0 := ne_of_gt hD
  field_simp

def NfPrev (D δ : ℝ) : ℝ := D / δ

def NfNew (δ : ℝ) : ℝ := 1 / δ ^ 2

theorem new_reduces_iff (D δ : ℝ) (hδ : 0 < δ) :
    NfNew δ < NfPrev D δ ↔ 1 / δ < D := by
  unfold NfNew NfPrev
  have hδ2 : (0 : ℝ) < δ ^ 2 := by positivity
  have key : (1 : ℝ) / δ ^ 2 < D / δ ↔ 1 < D * δ := by
    rw [div_lt_iff₀ hδ2]
    rw [show (D / δ) * δ ^ 2 = D * δ by
      rw [pow_two, ← mul_assoc, div_mul_cancel₀ D (ne_of_gt hδ)]]
  rw [key, div_lt_iff₀ hδ]

def scaleThreshold (l δrel : ℝ) : ℝ := (l * δrel)⁻¹

def relReductionFactor (l δrel D : ℝ) : ℝ := (l * δrel)⁻¹ / D

theorem relative_reduction_beneficial (l δrel D : ℝ) (hD : 0 < D) :
    relReductionFactor l δrel D < 1 ↔ scaleThreshold l δrel < D := by
  unfold relReductionFactor scaleThreshold
  exact div_lt_one₀ hD

theorem inner_qae_reduction_le (l δrel M D : ℝ) (hM : scaleThreshold l δrel ≤ M)
    (hD : 0 < D) : relReductionFactor l δrel D ≤ M / D := by
  unfold relReductionFactor scaleThreshold at *
  exact div_le_div_of_nonneg_right hM (le_of_lt hD)

end Qatlib.Papers.MonteCarloInt20.CostModels.LeadingQuery
