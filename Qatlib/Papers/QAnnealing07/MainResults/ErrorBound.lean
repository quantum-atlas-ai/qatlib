/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Final annealing error estimates

This module verifies the temperature substitution and numerical error budget used in the
final-measurement analysis of [SommaBoixoBarnum2007]. The theorem `eq19_error_le_eps` combines
the thermal term with an assumed phase-estimation error budget, while `eqA19_error_bound`
simplifies the classical norm estimate.

## Main statements

* `first_term_eq_eps_sq_half`: the thermal term equals `ε² / 2`.
* `eq19_error_le_eps`: the combined scalar error is at most `ε`.
* `eqA19_error_bound`: the classical norm-factor simplification.

## References

* [Somma et al., 2007][SommaBoixoBarnum2007]
-/

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators

namespace Qatlib.Papers.QAnnealing07.MainResults.ErrorBound

/-- With the specified logarithmic final inverse temperature and positive parameters, the
thermal term `d * exp (-(βf * γ))` equals `ε ^ 2 / 2` [SommaBoixoBarnum2007]. -/
theorem first_term_eq_eps_sq_half
    (d ε γ βf : ℝ) (hd : 0 < d) (hε : 0 < ε) (hγ : 0 < γ)
    (hβ : βf = Real.log (2 * d / ε ^ 2) / γ) :
    d * Real.exp (-(βf * γ)) = ε ^ 2 / 2 := by
  have harg : 0 < 2 * d / ε ^ 2 := by positivity
  have hβγ : βf * γ = Real.log (2 * d / ε ^ 2) := by
    rw [hβ]
    field_simp
  rw [hβγ, Real.exp_neg, Real.exp_log harg]
  field_simp

/-- For `0 < ε ≤ 1`, the specified final temperature and error budget `τ' * Q * ν ^ 2 ≤ ε / 2`
make the combined error expression at most `ε` [SommaBoixoBarnum2007]. -/
theorem eq19_error_le_eps
    (d ε γ βf τ' Q ν : ℝ) (hd : 0 < d) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hγ : 0 < γ) (hβ : βf = Real.log (2 * d / ε ^ 2) / γ)
    (hnum : τ' * Q * ν ^ 2 ≤ ε / 2) :
    d * Real.exp (-(βf * γ)) + τ' * Q * ν ^ 2 ≤ ε := by
  rw [first_term_eq_eps_sq_half d ε γ βf hd hε0 hγ hβ]
  have hsq : ε ^ 2 / 2 ≤ ε / 2 := by
    have := mul_nonneg hε0.le (sub_nonneg.mpr hε1)
    nlinarith
  linarith

/-- If `P` satisfies the given exponential bound with a nonnegative norm factor whose square is
at most two, then `P ≤ sqrt (2d) * exp (-(βf * γ / 2))` [SommaBoixoBarnum2007]. -/
theorem eqA19_error_bound
    (d βf γ P hnorm : ℝ)
    (hA4 : P ≤ Real.sqrt d * Real.exp (-(βf * γ / 2)) * hnorm)
    (hhnorm0 : 0 ≤ hnorm) (hhnorm : hnorm ^ 2 ≤ 2) :
    P ≤ Real.sqrt (2 * d) * Real.exp (-(βf * γ / 2)) := by
  have hs : hnorm ≤ Real.sqrt 2 := by
    calc hnorm = Real.sqrt (hnorm ^ 2) := (Real.sqrt_sq hhnorm0).symm
      _ ≤ Real.sqrt 2 := Real.sqrt_le_sqrt hhnorm
  have hexp : 0 ≤ Real.exp (-(βf * γ / 2)) := (Real.exp_pos _).le
  have hsqrt_d : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
  calc P ≤ Real.sqrt d * Real.exp (-(βf * γ / 2)) * hnorm := hA4
    _ ≤ Real.sqrt d * Real.exp (-(βf * γ / 2)) * Real.sqrt 2 := by
        exact mul_le_mul_of_nonneg_left hs (mul_nonneg hsqrt_d hexp)
    _ = Real.sqrt (2 * d) * Real.exp (-(βf * γ / 2)) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
        ring

end Qatlib.Papers.QAnnealing07.MainResults.ErrorBound
