/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FastPoisson19.CostModels.DimensionalComplexity

/-!
# Accuracy-dependent main complexity bounds

At `alpha = 1`, the grid-size logarithm becomes `log (1 / eps)`. The theorem
`modeled_main_complexity` uses this substitution and an upper bound on the amplification factor
to give explicit dimensional resource bounds. These statements concern the formulas and models
in [WangEtAl2020].

## Main statements

* `log_gridSize_one`: simplifies the grid-size logarithm.
* `modeled_main_complexity`: gives qubit and gate bounds in terms of accuracy and dimension.

## References

* [Wang et al., 2020][WangEtAl2020]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.FastPoisson19.CostModels

open Asymptotics Filter

/-- For positive `eps`, the logarithm of `gridSize eps 1` is `log (1 / eps)`. -/
lemma log_gridSize_one {eps : ℝ} (heps : 0 < eps) :
    Real.log (gridSize eps 1) = Real.log (1 / eps) := by
  unfold gridSize
  rw [Real.log_rpow heps]
  have h1 : Real.log (1 / eps) = -Real.log eps := by
    rw [one_div, Real.log_inv]
  rw [h1]
  ring

/-- For nonnegative `K`, bounds the qubit model by a constant times `d * log(1 / eps)^2` and,
when `0 ≤ kappa ≤ K`, the gate model by a constant times `K * d * log(1 / eps)^3`. These are
bounds on the explicit models associated with [WangEtAl2020]. -/
theorem modeled_main_complexity (K : ℝ) (_hK : 0 ≤ K) :
    (∀ d eps : ℝ, 0 ≤ d → 0 < eps → eps ≤ 1 →
      dimensionQubitsModel d (registerSize eps 1) (registerSize eps 1) ≤
        (2 / (Real.log 2) ^ 2) * d * (Real.log (1 / eps)) ^ 2) ∧
    (∀ d kappa eps : ℝ, 0 ≤ d → 0 ≤ kappa → kappa ≤ K → 0 < eps → eps ≤ 1 →
      dimensionGatesModel d kappa (registerSize eps 1) (registerSize eps 1) ≤
        (134 * K / (Real.log 2) ^ 3) * d * (Real.log (1 / eps)) ^ 3) := by
  refine ⟨?_, ?_⟩
  · intro d eps hd heps _
    rw [dimension_qubit_count_eq d eps 1 heps, log_gridSize_one heps]
  · intro d kappa eps hd hk hkK heps heps1
    rw [dimension_gate_count_eq d kappa eps 1 heps, log_gridSize_one heps]
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hL : (0 : ℝ) ≤ Real.log (1 / eps) := by
      apply Real.log_nonneg
      rw [one_div]; exact (one_le_inv₀ heps).mpr heps1
    have hL3 : (0 : ℝ) ≤ (Real.log (1 / eps)) ^ 3 := by positivity
    have hC : (0 : ℝ) ≤ 134 / (Real.log 2) ^ 3 := by positivity
    have hstep : (134 / (Real.log 2) ^ 3) * kappa ≤ 134 * K / (Real.log 2) ^ 3 := by
      have hprod := mul_le_mul_of_nonneg_right hkK hC
      calc (134 / (Real.log 2) ^ 3) * kappa = kappa * (134 / (Real.log 2) ^ 3) := by
            ring
        _ ≤ K * (134 / (Real.log 2) ^ 3) := hprod
        _ = 134 * K / (Real.log 2) ^ 3 := by ring
    have hdL : (0 : ℝ) ≤ d * (Real.log (1 / eps)) ^ 3 := mul_nonneg hd hL3
    calc (134 / (Real.log 2) ^ 3) * kappa * d * (Real.log (1 / eps)) ^ 3
        = ((134 / (Real.log 2) ^ 3) * kappa) * (d * (Real.log (1 / eps)) ^ 3) := by
          ring
      _ ≤ (134 * K / (Real.log 2) ^ 3) * (d * (Real.log (1 / eps)) ^ 3) :=
          mul_le_mul_of_nonneg_right hstep hdL
      _ = 134 * K / (Real.log 2) ^ 3 * d * (Real.log (1 / eps)) ^ 3 := by ring

end Qatlib.Papers.FastPoisson19.CostModels
