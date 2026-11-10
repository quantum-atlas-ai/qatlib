/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.CharZero.Defs
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
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.Positivity.Core

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

namespace Qatlib.Papers.QuantumSVM13.CostModels

noncomputable def modeledStepAccumulatedError (t0 T : ℝ) : ℝ := T * (t0 / T) ^ 2

noncomputable def modeledStepCount (t0 ε : ℝ) : ℝ := t0 ^ 2 / ε

noncomputable def modeledRelativeEigenvalueError (t0 lam : ℝ) : ℝ := 1 / (t0 * lam)

noncomputable def modeledEffectiveConditionNumber (εK : ℝ) : ℝ := 1 / εK

noncomputable def modeledTotalEvolutionTime (κ ε : ℝ) : ℝ := κ / ε

noncomputable def modeledRunTime (t0 ε M N : ℝ) : ℝ := t0 ^ 2 / ε * Real.log (M * N)

noncomputable def modeledRepeatedRunTime (κ ε M N : ℝ) : ℝ :=
  κ * (κ ^ 2 / ε ^ 3 * Real.log (M * N))

theorem modeledStepAccumulatedError_eq (t0 T : ℝ) (hT : T ≠ 0) :
    modeledStepAccumulatedError t0 T = t0 ^ 2 / T := by
  unfold modeledStepAccumulatedError
  field_simp

theorem modeledStepCount_achieves_epsilon (t0 ε : ℝ) (ht0 : t0 ≠ 0) (hε : ε ≠ 0) :
    modeledStepAccumulatedError t0 (modeledStepCount t0 ε) = ε := by
  unfold modeledStepAccumulatedError modeledStepCount
  field_simp

theorem modeledRelativeEigenvalueError_mono (t0 lam εK : ℝ) (ht0 : 0 < t0) (hεK : 0 < εK)
    (hlam : εK ≤ lam) :
    modeledRelativeEigenvalueError t0 lam ≤ modeledRelativeEigenvalueError t0 εK := by
  unfold modeledRelativeEigenvalueError
  have h1 : 0 < t0 * εK := mul_pos ht0 hεK
  have h2 : t0 * εK ≤ t0 * lam := by exact mul_le_mul_of_nonneg_left hlam ht0.le
  exact one_div_le_one_div_of_le h1 h2

theorem modeledRelativeEigenvalueError_le (lam εK ε : ℝ) (hεK : 0 < εK) (hε : 0 < ε)
    (hlam : εK ≤ lam) :
    modeledRelativeEigenvalueError (1 / (εK * ε)) lam ≤ ε := by
  have ht0 : 0 < 1 / (εK * ε) := by positivity
  have hmono := modeledRelativeEigenvalueError_mono (1 / (εK * ε)) lam εK ht0 hεK hlam
  have hval : modeledRelativeEigenvalueError (1 / (εK * ε)) εK = ε := by
    unfold modeledRelativeEigenvalueError
    field_simp
  rw [hval] at hmono
  exact hmono

theorem modeledTotalEvolutionTime_eq (εK ε : ℝ) :
    modeledTotalEvolutionTime (modeledEffectiveConditionNumber εK) ε = 1 / (εK * ε) := by
  unfold modeledTotalEvolutionTime modeledEffectiveConditionNumber
  rw [div_div]

theorem modeledRunTime_eq (κ ε M N : ℝ) (hε : ε ≠ 0) :
    modeledRunTime (modeledTotalEvolutionTime κ ε) ε M N
      = κ ^ 2 / ε ^ 3 * Real.log (M * N) := by
  unfold modeledRunTime modeledTotalEvolutionTime
  field_simp

theorem modeledRepeatedRunTime_eq (κ ε M N : ℝ) (_hκ : κ ≠ 0) (hε : ε ≠ 0) :
    modeledRepeatedRunTime κ ε M N = κ ^ 3 / ε ^ 3 * Real.log (M * N) := by
  unfold modeledRepeatedRunTime
  field_simp

theorem modeledRepeatedRunTime_kappa (εK ε M N : ℝ) (hεK : εK ≠ 0) (hε : ε ≠ 0) :
    modeledRepeatedRunTime (modeledEffectiveConditionNumber εK) ε M N
      = 1 / (εK ^ 3 * ε ^ 3) * Real.log (M * N) := by
  unfold modeledRepeatedRunTime modeledEffectiveConditionNumber
  field_simp

end Qatlib.Papers.QuantumSVM13.CostModels
