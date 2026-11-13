/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FastPoisson19.CostModels.CircuitCostDefs

/-!
# Controlled-rotation resource bounds

The explicit controlled-rotation models satisfy quadratic qubit and cubic gate upper bounds on
the stated parameter ranges. These estimates also imply the little-o comparisons with cubic and
quartic powers recorded by `modeled_controlled_rotation_cost`. These statements concern the
formulas and models in [WangEtAl2020].

## Main statements

* `controlled_rotation_qubit_le`: bounds the qubit model by `6 * m^2` for `m ≥ 1`.
* `controlled_rotation_gate_le`: bounds the gate model by `34 * m^3` for `m ≥ 2`.
* `modeled_controlled_rotation_cost`: packages the pointwise and asymptotic bounds.

## References

* [Wang et al., 2020][WangEtAl2020]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.FastPoisson19.CostModels

open Asymptotics Filter

/-- For a real number at least one, the number is at most its square. -/
private lemma le_sq_of_one_le {m : ℝ} (hm : 1 ≤ m) : m ≤ m ^ 2 := by
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have := mul_le_mul_of_nonneg_left hm hm0
  simpa [pow_two] using this

/-- For a real number at least one, its square is at most its cube. -/
private lemma sq_le_cube_of_one_le {m : ℝ} (hm : 1 ≤ m) : m ^ 2 ≤ m ^ 3 := by
  have hm0 : (0 : ℝ) ≤ m ^ 2 := sq_nonneg m
  have := mul_le_mul_of_nonneg_left hm hm0
  simpa [pow_succ, pow_two, mul_assoc] using this

/-- For `m ≥ 1`, the controlled-rotation qubit model is at most `6 * m^2`. -/
theorem controlled_rotation_qubit_le (m : ℝ) (hm : 1 ≤ m) :
    controlledRotationQubitsModel m ≤ 6 * m ^ 2 := by
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have hmm := le_sq_of_one_le hm
  have hone : (1 : ℝ) ≤ m ^ 2 := by nlinarith [hmm, hm]
  unfold controlledRotationQubitsModel
  nlinarith [hmm, hone, hm0]

/-- For `m ≥ 2`, the controlled-rotation gate model is at most `34 * m^3`. -/
theorem controlled_rotation_gate_le (m : ℝ) (hm : 2 ≤ m) :
    controlledRotationGatesModel m ≤ 34 * m ^ 3 := by
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have hm1 : (1 : ℝ) ≤ m := by linarith
  have hmm := le_sq_of_one_le hm1
  unfold controlledRotationGatesModel
  nlinarith [mul_le_mul_of_nonneg_left hmm hm0]

/-- The controlled-rotation gate model is nonnegative for `m ≥ 2`. -/
theorem controlled_rotation_gate_nonneg (m : ℝ) (hm : 2 ≤ m) :
    0 ≤ controlledRotationGatesModel m := by
  have hm1 : (1 : ℝ) ≤ m := by linarith
  have hmm := le_sq_of_one_le hm1
  have hm2 := sq_le_cube_of_one_le hm1
  unfold controlledRotationGatesModel
  nlinarith [hmm, hm2]

/-- The controlled-rotation qubit model is little-o of `m^3` as `m` tends to infinity. -/
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

/-- The controlled-rotation gate model is little-o of `m^4` as `m` tends to infinity. -/
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

/-- Combines the quadratic qubit bound, cubic gate bound, and the corresponding little-o
comparisons for the controlled-rotation models of [WangEtAl2020]. -/
theorem modeled_controlled_rotation_cost :
    (∀ m : ℝ, 1 ≤ m → controlledRotationQubitsModel m ≤ 6 * m ^ 2) ∧
    (∀ m : ℝ, 2 ≤ m → controlledRotationGatesModel m ≤ 34 * m ^ 3) ∧
    (fun m : ℝ => controlledRotationQubitsModel m) =o[atTop] (fun m : ℝ => m ^ 3) ∧
    (fun m : ℝ => controlledRotationGatesModel m) =o[atTop] (fun m : ℝ => m ^ 4) :=
  ⟨controlled_rotation_qubit_le, controlled_rotation_gate_le,
    controlled_rotation_qubit_littleO, controlled_rotation_gate_littleO⟩

end Qatlib.Papers.FastPoisson19.CostModels
