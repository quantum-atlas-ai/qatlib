/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt

/-!
# Scalar Zeno success estimates

This module proves the scalar product and squared-amplitude bounds used in the Zeno preparation
analysis of [SommaBoixoBarnum2007]. Explicit assumptions on the step size, step count, and
per-step loss yield lower bounds linear in the accumulated error budget.

## Main statements

* `zeno_success_probability`: a product lower bound from a bounded total step scale.
* `eqB12_amplitude_lower_bound`: the squared-amplitude estimate of Equation (B12).
* `eqB12_success_lower_bound`: the same estimate with the success-bound coefficient order.

## References

* [Somma et al., 2007][SommaBoixoBarnum2007]
-/

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators

namespace Qatlib.Papers.QAnnealing07.MainResults.Zeno

/-- For positive `ν`, nonnegative `c`, per-step loss at most one, and `Q * ν ≤ C`, the product
`(1 - c * ν ^ 2) ^ Q` is at least `1 - c * C * ν` [SommaBoixoBarnum2007]. -/
theorem zeno_success_probability (ν c C : ℝ) (Q : ℕ)
    (hν : 0 < ν) (hc : 0 ≤ c) (hQν : (Q : ℝ) * ν ≤ C) (hcν : c * ν ^ 2 ≤ 1) :
    1 - c * C * ν ≤ (1 - c * ν ^ 2) ^ Q := by
  have hbern : 1 + (Q : ℝ) * (-(c * ν ^ 2)) ≤ (1 + -(c * ν ^ 2)) ^ Q :=
    one_add_mul_le_pow (a := -(c * ν ^ 2)) (by linarith) Q
  have hQc : (Q : ℝ) * (c * ν ^ 2) ≤ c * C * ν := by
    have hνc : 0 ≤ c * ν := mul_nonneg hc hν.le
    calc (Q : ℝ) * (c * ν ^ 2) = ((Q : ℝ) * ν) * (c * ν) := by ring_nf
      _ ≤ C * (c * ν) := mul_le_mul_of_nonneg_right hQν hνc
      _ = c * C * ν := by ring_nf
  have hbase : (1 + -(c * ν ^ 2)) = 1 - c * ν ^ 2 := by ring_nf
  calc 1 - c * C * ν ≤ 1 - (Q : ℝ) * (c * ν ^ 2) := by linarith
    _ = 1 + (Q : ℝ) * (-(c * ν ^ 2)) := by ring_nf
    _ ≤ (1 + -(c * ν ^ 2)) ^ Q := hbern
    _ = (1 - c * ν ^ 2) ^ Q := by rw [hbase]

/-- For `Q ≥ 1` and `0 ≤ c * ν ^ 2 ≤ 1`, the displayed squared corrected amplitude is at least
`1 - 4 * Q * c * ν ^ 2` [SommaBoixoBarnum2007]. -/
theorem eqB12_amplitude_lower_bound (ν c : ℝ) (Q : ℕ)
    (hν : 0 < ν) (hc : 0 ≤ c) (hcν : c * ν ^ 2 ≤ 1) (hQ : 1 ≤ Q) :
    1 - 4 * (Q : ℝ) * c * ν ^ 2 ≤
      ((1 - c * ν ^ 2) ^ Q - ((Q : ℝ) - 1) * (c * ν ^ 2)) ^ 2 := by
  set x := c * ν ^ 2 with hx
  have hx0 : 0 ≤ x := by ring_nf; positivity
  have hx1 : x ≤ 1 := hcν
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hbern : 1 - (Q : ℝ) * x ≤ (1 - x) ^ Q := by
    have h := one_add_mul_le_pow (a := -x) (by linarith) Q
    have hbase : 1 + -x = 1 - x := by ring_nf
    rw [hbase] at h
    linarith [h]
  set base : ℝ := (1 - x) ^ Q - ((Q : ℝ) - 1) * x with hbase_def
  have hbase_lb : 1 - 2 * ((Q : ℝ) * x) ≤ base := by
    have h1 : (1 - x) ^ Q - ((Q : ℝ) - 1) * x
        ≥ 1 - (Q : ℝ) * x - ((Q : ℝ) - 1) * x := by linarith
    have h2 : 1 - (Q : ℝ) * x - ((Q : ℝ) - 1) * x
        = 1 - 2 * ((Q : ℝ) * x) + x := by ring_nf
    rw [hbase_def]
    linarith [h1, h2, hx0]
  have hbase_le : base ≤ 1 := by
    have hp : (1 - x) ^ Q ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have hsub : 0 ≤ ((Q : ℝ) - 1) * x := mul_nonneg (by linarith) hx0
    rw [hbase_def]
    linarith
  by_cases hy : (Q : ℝ) * x ≤ 1 / 4
  · have hpos : 0 ≤ 1 - 2 * ((Q : ℝ) * x) := by linarith
    have hsq : (1 - 2 * ((Q : ℝ) * x)) * (1 - 2 * ((Q : ℝ) * x)) ≤ base * base :=
      mul_self_le_mul_self hpos hbase_lb
    have hsq2 : 1 - 4 * (Q : ℝ) * x ≤ (1 - 2 * ((Q : ℝ) * x)) ^ 2 := by
      nlinarith [sq_nonneg ((Q : ℝ) * x)]
    calc 1 - 4 * (Q : ℝ) * c * ν ^ 2 = 1 - 4 * (Q : ℝ) * x := by rw [hx]; ring_nf
      _ ≤ (1 - 2 * ((Q : ℝ) * x)) ^ 2 := hsq2
      _ = (1 - 2 * ((Q : ℝ) * x)) * (1 - 2 * ((Q : ℝ) * x)) := by ring_nf
      _ ≤ base * base := hsq
      _ = base ^ 2 := by ring_nf
  · have hgt : 1 / 4 < (Q : ℝ) * x := lt_of_not_ge hy
    have hneg : 1 - 4 * (Q : ℝ) * x < 0 := by linarith
    have hsq0 : 0 ≤ base ^ 2 := sq_nonneg base
    calc 1 - 4 * (Q : ℝ) * c * ν ^ 2 = 1 - 4 * (Q : ℝ) * x := by rw [hx]; ring_nf
      _ ≤ 0 := le_of_lt hneg
      _ ≤ base ^ 2 := hsq0

/-- Under the stated step-size and step-count assumptions, the displayed squared corrected
amplitude is at least `1 - 4 * c * Q * ν ^ 2` [SommaBoixoBarnum2007]. -/
theorem eqB12_success_lower_bound (ν c : ℝ) (Q : ℕ)
    (hν : 0 < ν) (hc : 0 ≤ c) (hcν : c * ν ^ 2 ≤ 1) (hQ : 1 ≤ Q) :
    1 - 4 * c * (Q : ℝ) * ν ^ 2 ≤
      ((1 - c * ν ^ 2) ^ Q - ((Q : ℝ) - 1) * (c * ν ^ 2)) ^ 2 := by
  have h := eqB12_amplitude_lower_bound ν c Q hν hc hcν hQ
  calc 1 - 4 * c * (Q : ℝ) * ν ^ 2 = 1 - 4 * (Q : ℝ) * c * ν ^ 2 := by ring_nf
    _ ≤ _ := h

end Qatlib.Papers.QAnnealing07.MainResults.Zeno
