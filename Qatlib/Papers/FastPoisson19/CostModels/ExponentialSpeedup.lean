/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FastPoisson19.CostModels.CircuitCostDefs

/-!
# Exponential separation of dimensional cost models

The classical model is rewritten as an exponential in the dimension using `log_gridSize_eq`. For
fixed positive `alpha` and accuracy strictly between zero and one, its ratio to `d * (log
gridSize)^3` tends to infinity. These statements concern the formulas and models in
[WangEtAl2020].

## Main statements

* `classicalDimensionalModel_eq_exp`: gives the exponential form of the classical model.
* `modeled_exponential_separation`: proves divergence of the ratio as dimension increases.

## References

* [Wang et al., 2020][WangEtAl2020]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.FastPoisson19.CostModels

open Asymptotics Filter

/-- For positive `eps`, the logarithm of grid size is `alpha * log (1 / eps)`. -/
lemma log_gridSize_eq {eps alpha : ℝ} (heps : 0 < eps) :
    Real.log (gridSize eps alpha) = alpha * Real.log (1 / eps) := by
  unfold gridSize
  rw [Real.log_rpow heps]
  have h1 : Real.log (1 / eps) = -Real.log eps := by
    rw [one_div, Real.log_inv]
  rw [h1]
  ring

/-- For positive `eps`, the classical dimensional model is `exp (alpha * log (1 / eps) * d)`. -/
lemma classicalDimensionalModel_eq_exp {eps alpha : ℝ} (heps : 0 < eps) (d : ℕ) :
    classicalDimensionalModel eps alpha d =
      Real.exp (alpha * Real.log (1 / eps) * (d : ℝ)) := by
  unfold classicalDimensionalModel gridSize
  rw [Real.rpow_def_of_pos (Real.rpow_pos_of_pos heps (-alpha))]
  congr 1
  rw [Real.log_rpow heps]
  have h1 : Real.log (1 / eps) = -Real.log eps := by
    rw [one_div, Real.log_inv]
  rw [h1]
  ring

/-- For fixed positive `alpha` and `0 < eps < 1`, the ratio of the classical model to `d * (log
gridSize)^3` tends to infinity with natural dimension. This establishes the stated
separation of the cost models from [WangEtAl2020]. -/
theorem modeled_exponential_separation (alpha eps : ℝ) (halpha : 0 < alpha)
    (heps : 0 < eps) (heps1 : eps < 1) :
    Tendsto (fun d : ℕ => classicalDimensionalModel eps alpha d /
      ((d : ℝ) * (Real.log (gridSize eps alpha)) ^ 3)) atTop atTop := by
  have hb : 0 < alpha * Real.log (1 / eps) := by
    refine mul_pos halpha ?_
    have h1 : (1 : ℝ) < 1 / eps := by
      rw [one_div]
      exact (one_lt_inv₀ heps).mpr heps1
    exact Real.log_pos h1
  set b : ℝ := alpha * Real.log (1 / eps) with hbdef
  have hbpos : 0 < b := hb
  have hbd : Tendsto (fun d : ℕ => b * (d : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hbpos
  have hexpDiv : Tendsto (fun x : ℝ => Real.exp x / x) atTop atTop := by
    have h := Real.tendsto_exp_div_pow_atTop 1
    simpa [pow_one] using h
  have hcomp : Tendsto (fun d : ℕ => Real.exp (b * (d : ℝ)) / (b * (d : ℝ)))
      atTop atTop :=
    hexpDiv.comp hbd
  have hconst : Tendsto
      (fun d : ℕ => (1 / b ^ 2) * (Real.exp (b * (d : ℝ)) / (b * (d : ℝ))))
      atTop atTop :=
    hcomp.const_mul_atTop (by positivity)
  refine hconst.congr fun d => ?_
  rw [classicalDimensionalModel_eq_exp heps d, log_gridSize_eq heps]
  have hb_eq : b = alpha * Real.log (1 / eps) := hbdef
  rw [← hb_eq]
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp
  · have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    have hbne : b ≠ 0 := hbpos.ne'
    field_simp

end Qatlib.Papers.FastPoisson19.CostModels
