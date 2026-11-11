/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AndersonLoc09.MainResults.Defs

/-!
# Exact identities for the minimal-gap expression

This module rewrites real powers of `A * lambdaStar N f2` as the exponential gap expression,
including the specialization `n = vAlpha α * N`. It also bounds the reciprocal squared gap from
below under an explicit logarithmic condition [AltshulerKroviRoland2010].

## Main statements

* `minimal_gap_eq9`: proves the exact exponential identity underlying Equation (9).
* `adiabatic_time_ge_exp`: derives a reciprocal-square lower bound from a logarithmic condition.

## References

* [Altshuler et al., 2010][AltshulerKroviRoland2010]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AndersonLoc09.MainResults

open Real

/-- For positive `A`, `f2`, and `N`, the real power `(A * lambdaStar N f2) ^ n` equals `exp (-(n
/ 8) * log (N / N0 A f2))`, the expression in Equation (9) [AltshulerKroviRoland2010]. -/
theorem minimal_gap_eq9 (A f2 N n : ℝ) (hA : 0 < A) (hf2 : 0 < f2) (hN : 0 < N) :
    Real.rpow (A * lambdaStar N f2) n
      = Real.exp (-(n / 8) * Real.log (N / N0 A f2)) := by
  set c : ℝ := A * Real.sqrt 2 * Real.rpow f2 (-(1 / 4)) with hc_def
  have hcpos : 0 < c := by
    rw [hc_def]
    exact mul_pos (mul_pos hA (Real.sqrt_pos.mpr (by norm_num)))
      (Real.rpow_pos_of_pos hf2 _)
  have hN0pos : 0 < N0 A f2 := by
    unfold N0
    positivity
  have hp8 : c ^ 8 = N0 A f2 := by
    rw [hc_def]
    exact prefactor_pow_eight A f2 hA hf2
  have hlogc : Real.log c = (1 / 8) * Real.log (N0 A f2) := by
    have h := congrArg Real.log hp8
    rw [Real.log_pow] at h
    linear_combination (1 / 8) * h
  have hAlam : A * lambdaStar N f2 = c * Real.rpow N (-(1 / 8)) := by
    rw [hc_def]
    unfold lambdaStar
    ring
  rw [hAlam]
  have hNpowpos : 0 < Real.rpow N (-(1 / 8)) := Real.rpow_pos_of_pos hN _
  have hprodpos : 0 < c * Real.rpow N (-(1 / 8)) := mul_pos hcpos hNpowpos
  rw [rpow_def_fn hprodpos n]
  have hlogN : Real.log (Real.rpow N (-(1 / 8))) = -(1 / 8) * Real.log N := by
    simpa using Real.log_rpow hN (-(1 / 8))
  have hlogprod : Real.log (c * Real.rpow N (-(1 / 8)))
      = Real.log c + Real.log (Real.rpow N (-(1 / 8))) := by
    simpa using Real.log_mul (ne_of_gt hcpos) (ne_of_gt hNpowpos)
  rw [hlogprod, hlogN, hlogc]
  have hdiv : Real.log (N / N0 A f2) = Real.log N - Real.log (N0 A f2) :=
    Real.log_div (ne_of_gt hN) (ne_of_gt hN0pos)
  rw [hdiv]
  congr 1
  ring

/-- For positive `A`, `f2`, and `N`, substituting exponent `vAlpha α * N` into the threshold
power gives the corresponding `gapFormula` [AltshulerKroviRoland2010]. -/
theorem minimal_gap_eq9_vAlpha (A f2 α N : ℝ) (hA : 0 < A) (hf2 : 0 < f2)
    (hN : 0 < N) :
    Real.rpow (A * lambdaStar N f2) (vAlpha α * N)
      = gapFormula (vAlpha α * N) N (N0 A f2) := by
  rw [minimal_gap_eq9 A f2 N (vAlpha α * N) hA hf2 hN]
  rfl

/-- For positive `N0`, `v`, and `N`, the condition `1 ≤ (v / 4) * log (N / N0)` implies that the
reciprocal squared gap formula is at least `exp N` [AltshulerKroviRoland2010]. -/
theorem adiabatic_time_ge_exp (N0 v N : ℝ) (hN0 : 0 < N0) (hv : 0 < v) (hN : 0 < N)
    (hcond : 1 ≤ (v / 4) * Real.log (N / N0)) :
    Real.exp N ≤ 1 / (gapFormula (v * N) N N0) ^ 2 := by
  have hgap_pos : 0 < gapFormula (v * N) N N0 := by
    unfold gapFormula
    positivity
  unfold gapFormula
  have hsq : (Real.exp (-(v * N / 8) * Real.log (N / N0))) ^ 2
      = Real.exp (-(v * N / 4) * Real.log (N / N0)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hsq, one_div, ← Real.exp_neg]
  rw [Real.exp_le_exp]
  rw [show -(-(v * N / 4) * Real.log (N / N0))
        = (v * N / 4) * Real.log (N / N0) by ring]
  have heq : (v * N / 4) * Real.log (N / N0) = N * ((v / 4) * Real.log (N / N0)) := by
    ring
  rw [heq]
  calc N = N * 1 := by ring
    _ ≤ N * ((v / 4) * Real.log (N / N0)) :=
        mul_le_mul_of_nonneg_left hcond (le_of_lt hN)

end Qatlib.Papers.AndersonLoc09.MainResults
