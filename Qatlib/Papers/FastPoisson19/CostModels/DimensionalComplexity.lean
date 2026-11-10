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

theorem dimension_qubit_count_eq (d eps alpha : ℝ) (heps : 0 < eps) :
    dimensionQubitsModel d (registerSize eps alpha) (registerSize eps alpha) =
      (2 / (Real.log 2) ^ 2) * d * (Real.log (gridSize eps alpha)) ^ 2 := by
  unfold dimensionQubitsModel oneDimQubitsModel
  rw [registerSize_eq_log_gridSize heps]
  field_simp
  ring

theorem dimension_gate_count_eq (d kappa eps alpha : ℝ) (heps : 0 < eps) :
    dimensionGatesModel d kappa (registerSize eps alpha) (registerSize eps alpha) =
      (134 / (Real.log 2) ^ 3) * kappa * d * (Real.log (gridSize eps alpha)) ^ 3 := by
  unfold dimensionGatesModel oneDimGatesModel
  rw [registerSize_eq_log_gridSize heps]
  field_simp
  ring

theorem modeled_dimensional_complexity (alpha : ℝ) :
    (∀ d eps : ℝ, 0 ≤ d → 0 < eps →
      dimensionQubitsModel d (registerSize eps alpha) (registerSize eps alpha) ≤
        (2 / (Real.log 2) ^ 2) * d * (Real.log (gridSize eps alpha)) ^ 2) ∧
    (∀ d kappa eps : ℝ, 0 ≤ kappa → 0 < eps →
      dimensionGatesModel d kappa (registerSize eps alpha) (registerSize eps alpha) ≤
        (134 / (Real.log 2) ^ 3) * kappa * d *
          (Real.log (gridSize eps alpha)) ^ 3) := by
  refine ⟨fun d eps _ heps => ?_, fun d kappa eps _ heps => ?_⟩
  · rw [dimension_qubit_count_eq d eps alpha heps]
  · rw [dimension_gate_count_eq d kappa eps alpha heps]

theorem dimension_qubit_isBigO (alpha : ℝ) {ι : Type*} (l : Filter ι)
    (d eps : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (heps : ∀ i, 0 < eps i) :
    (fun i => dimensionQubitsModel (d i) (registerSize (eps i) alpha)
        (registerSize (eps i) alpha))
      =O[l] (fun i => d i * (Real.log (gridSize (eps i) alpha)) ^ 2) := by
  refine IsBigO.of_bound |2 / (Real.log 2) ^ 2| (Eventually.of_forall fun i => ?_)
  have heq := dimension_qubit_count_eq (d i) (eps i) alpha (heps i)
  set L : ℝ := Real.log (gridSize (eps i) alpha) with hL
  have hL2 : (0 : ℝ) ≤ L ^ 2 := sq_nonneg L
  have hdL : (0 : ℝ) ≤ d i * L ^ 2 := mul_nonneg (hd i) hL2
  rw [Real.norm_eq_abs, Real.norm_eq_abs, heq]
  simp only [abs_mul, abs_of_nonneg (hd i), abs_of_nonneg hL2, abs_of_nonneg hdL]
  nlinarith

theorem dimension_gate_isBigO (alpha : ℝ) {ι : Type*} (l : Filter ι)
    (d kappa eps : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (hk : ∀ i, 0 ≤ kappa i)
    (heps : ∀ i, 0 < eps i) :
    (fun i => dimensionGatesModel (d i) (kappa i) (registerSize (eps i) alpha)
        (registerSize (eps i) alpha))
      =O[l] (fun i => kappa i * d i * (Real.log (gridSize (eps i) alpha)) ^ 3) := by
  refine IsBigO.of_bound |134 / (Real.log 2) ^ 3| (Eventually.of_forall fun i => ?_)
  have heq := dimension_gate_count_eq (d i) (kappa i) (eps i) alpha (heps i)
  set L : ℝ := Real.log (gridSize (eps i) alpha) with hL
  rw [Real.norm_eq_abs, Real.norm_eq_abs, heq]
  simp only [abs_mul, abs_of_nonneg (hk i), abs_of_nonneg (hd i)]
  nlinarith

end Qatlib.Papers.FastPoisson19.CostModels
