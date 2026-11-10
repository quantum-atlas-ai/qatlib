/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FastPoisson19.CostModels.CircuitCostDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.FastPoisson19.CostModels

open Asymptotics Filter

private lemma le_sq_of_one_le {m : ℝ} (hm : 1 ≤ m) : m ≤ m ^ 2 := by
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have := mul_le_mul_of_nonneg_left hm hm0
  simpa [pow_two] using this

private lemma sq_le_cube_of_one_le {m : ℝ} (hm : 1 ≤ m) : m ^ 2 ≤ m ^ 3 := by
  have hm0 : (0 : ℝ) ≤ m ^ 2 := sq_nonneg m
  have := mul_le_mul_of_nonneg_left hm hm0
  simpa [pow_succ, pow_two, mul_assoc] using this

theorem controlled_rotation_qubit_le (m : ℝ) (hm : 1 ≤ m) :
    controlledRotationQubitsModel m ≤ 6 * m ^ 2 := by
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have hmm := le_sq_of_one_le hm
  have hone : (1 : ℝ) ≤ m ^ 2 := by nlinarith [hmm, hm]
  unfold controlledRotationQubitsModel
  nlinarith [hmm, hone, hm0]

theorem controlled_rotation_gate_le (m : ℝ) (hm : 2 ≤ m) :
    controlledRotationGatesModel m ≤ 34 * m ^ 3 := by
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have hm1 : (1 : ℝ) ≤ m := by linarith
  have hmm := le_sq_of_one_le hm1
  unfold controlledRotationGatesModel
  nlinarith [mul_le_mul_of_nonneg_left hmm hm0]

theorem controlled_rotation_gate_nonneg (m : ℝ) (hm : 2 ≤ m) :
    0 ≤ controlledRotationGatesModel m := by
  have hm1 : (1 : ℝ) ≤ m := by linarith
  have hmm := le_sq_of_one_le hm1
  have hm2 := sq_le_cube_of_one_le hm1
  unfold controlledRotationGatesModel
  nlinarith [hmm, hm2]

theorem controlled_rotation_qubit_littleO :
    (fun m : ℝ => controlledRotationQubitsModel m) =o[atTop] (fun m : ℝ => m ^ 3) := by
  rw [isLittleO_iff]
  intro c hc
  filter_upwards [eventually_ge_atTop (max 1 (6 / c))] with m hm
  have hm1 : (1 : ℝ) ≤ m := le_trans (le_max_left _ _) hm
  have hm6 : 6 / c ≤ m := le_trans (le_max_right _ _) hm
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have hq : 0 ≤ controlledRotationQubitsModel m := controlledRotationQubitsModel_nonneg hm0
  have hle := controlled_rotation_qubit_le m hm1
  have h6m : 6 ≤ c * m := by
    have := (div_le_iff₀ hc).mp hm6
    linarith
  have hprod := mul_le_mul_of_nonneg_right h6m (sq_nonneg m)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hq, abs_of_nonneg (by positivity)]
  nlinarith

theorem controlled_rotation_gate_littleO :
    (fun m : ℝ => controlledRotationGatesModel m) =o[atTop] (fun m : ℝ => m ^ 4) := by
  rw [isLittleO_iff]
  intro c hc
  filter_upwards [eventually_ge_atTop (max 2 (34 / c))] with m hm
  have hm2 : (2 : ℝ) ≤ m := le_trans (le_max_left _ _) hm
  have hm34 : 34 / c ≤ m := le_trans (le_max_right _ _) hm
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have hg : 0 ≤ controlledRotationGatesModel m := controlled_rotation_gate_nonneg m hm2
  have hle := controlled_rotation_gate_le m hm2
  have h34m : 34 ≤ c * m := by
    have := (div_le_iff₀ hc).mp hm34
    linarith
  have hprod : 34 * m ^ 3 ≤ (c * m) * m ^ 3 :=
    mul_le_mul_of_nonneg_right h34m (by positivity)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hg, abs_of_nonneg (by positivity)]
  nlinarith

theorem modeled_controlled_rotation_cost :
    (∀ m : ℝ, 1 ≤ m → controlledRotationQubitsModel m ≤ 6 * m ^ 2) ∧
    (∀ m : ℝ, 2 ≤ m → controlledRotationGatesModel m ≤ 34 * m ^ 3) ∧
    (fun m : ℝ => controlledRotationQubitsModel m) =o[atTop] (fun m : ℝ => m ^ 3) ∧
    (fun m : ℝ => controlledRotationGatesModel m) =o[atTop] (fun m : ℝ => m ^ 4) :=
  ⟨controlled_rotation_qubit_le, controlled_rotation_gate_le,
    controlled_rotation_qubit_littleO, controlled_rotation_gate_littleO⟩

end Qatlib.Papers.FastPoisson19.CostModels
