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

theorem one_dim_qubit_le (m n : ℝ) (hn : 1 ≤ n) (hmn : n ≤ m) :
    oneDimQubitsModel m n ≤ 2 * m ^ 2 := by
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have hnm : n * m ≤ m * m := mul_le_mul_of_nonneg_right hmn hm0
  unfold oneDimQubitsModel
  nlinarith

theorem one_dim_gate_le (m n : ℝ) (hn : 1 ≤ n) (hmn : n ≤ m) :
    oneDimGatesModel m n ≤ 134 * m ^ 3 := by
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have hnm : n * m ^ 2 ≤ m * m ^ 2 := mul_le_mul_of_nonneg_right hmn (by positivity)
  unfold oneDimGatesModel
  nlinarith

theorem one_dim_amplified_gate_le (m n kappa : ℝ) (hn : 1 ≤ n) (hmn : n ≤ m)
    (hk : 0 ≤ kappa) :
    kappa * oneDimGatesModel m n ≤ 134 * (kappa * m ^ 3) := by
  have h := one_dim_gate_le m n hn hmn
  nlinarith [mul_le_mul_of_nonneg_left h hk]

theorem modeled_one_dim_complexity (m n kappa : ℕ → ℝ)
    (hn : ∀ t, 1 ≤ n t) (hmn : ∀ t, n t ≤ m t) (hk : ∀ t, 0 ≤ kappa t) :
    (fun t => oneDimQubitsModel (m t) (n t)) =O[atTop] (fun t => (m t) ^ 2) ∧
    (fun t => oneDimGatesModel (m t) (n t)) =O[atTop] (fun t => (m t) ^ 3) ∧
    (fun t => kappa t * oneDimGatesModel (m t) (n t)) =O[atTop]
      (fun t => kappa t * (m t) ^ 3) := by
  have hm0 : ∀ t, 0 ≤ m t := fun t => le_trans (by linarith [hn t]) (hmn t)
  refine ⟨?_, ?_, ?_⟩
  · refine IsBigO.of_bound 2 (Eventually.of_forall fun t => ?_)
    have h := one_dim_qubit_le (m t) (n t) (hn t) (hmn t)
    have hq : 0 ≤ oneDimQubitsModel (m t) (n t) :=
      oneDimQubitsModel_nonneg (hm0 t) (le_trans (by norm_num) (hn t))
    rw [Real.norm_eq_abs, abs_of_nonneg hq, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (m t))]
    linarith
  · refine IsBigO.of_bound 134 (Eventually.of_forall fun t => ?_)
    have h := one_dim_gate_le (m t) (n t) (hn t) (hmn t)
    have hg : 0 ≤ oneDimGatesModel (m t) (n t) :=
      oneDimGatesModel_nonneg (hm0 t) (le_trans (by norm_num) (hn t))
    rw [Real.norm_eq_abs, abs_of_nonneg hg, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (hm0 t) 3)]
    linarith
  · refine IsBigO.of_bound 134 (Eventually.of_forall fun t => ?_)
    have h := one_dim_amplified_gate_le (m t) (n t) (kappa t) (hn t) (hmn t) (hk t)
    have hkg : 0 ≤ kappa t * oneDimGatesModel (m t) (n t) :=
      mul_nonneg (hk t) (oneDimGatesModel_nonneg (hm0 t) (le_trans (by norm_num) (hn t)))
    rw [Real.norm_eq_abs, abs_of_nonneg hkg, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hk t) (pow_nonneg (hm0 t) 3))]
    linarith

end Qatlib.Papers.FastPoisson19.CostModels
