/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.GraphModelMath.SrgQuotient.Defs
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# Strongly regular graph parameter bounds

This module proves the parameter facts used in the search analysis of [JanmarkMeyerWong2014] for
an actual finite strongly regular graph. `source_param_identity` states the natural-number
counting identity k * (k - ℓ - 1) = (n - k - 1) * μ for positive order n.

When k ≥ 1 and μ ≥ 1, `source_degree_lower_bound` derives sqrt(n) < k + 1. This provides an
explicit finite degree estimate.

## Main statements

* `source_param_identity`: the strongly regular graph parameter-counting identity.
* `source_degree_lower_bound`: the strict square-root lower bound on the degree plus one.

## References

* [Janmark et al., 2014][JanmarkMeyerWong2014]
-/

set_option autoImplicit false

namespace Qatlib.Papers.NoGlobalSym14.ParamFacts

open SimpleGraph

/-- A finite strongly regular graph of positive order satisfies k * (k - ℓ - 1) = (n - k - 1) *
μ in natural-number arithmetic, the parameter identity in [Janmark et al., Eq.
(2)][JanmarkMeyerWong2014]. -/
theorem source_param_identity {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {n k ℓ μ : ℕ} (h : G.IsSRGWith n k ℓ μ) (hn : 0 < n) :
    k * (k - ℓ - 1) = (n - k - 1) * μ :=
  Qatlib.Foundations.GraphModelMath.SrgQuotient.parameter_identity G h hn

/-- For a finite strongly regular graph of positive order with k ≥ 1 and μ ≥ 1, sqrt(n) < k + 1,
giving the finite degree estimate associated with [Janmark et al., Eq.
(3)][JanmarkMeyerWong2014]. -/
theorem source_degree_lower_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {n k ℓ μ : ℕ} (h : G.IsSRGWith n k ℓ μ)
    (hn : 0 < n) (hk : 1 ≤ k) (hμ : 1 ≤ μ) :
    Real.sqrt (n : ℝ) < (k : ℝ) + 1 := by

  have hparam : k * (k - ℓ - 1) = (n - k - 1) * μ := source_param_identity G h hn

  have hstep1 : k * (k - ℓ - 1) ≤ k * (k - 1) := by
    apply Nat.mul_le_mul_left
    omega

  have hstep2 : k * (k - 1) < k * k := by
    have : k - 1 < k := by omega
    exact Nat.mul_lt_mul_of_pos_left this hk

  have hmul : (n - k - 1) * μ < k * k := by
    rw [← hparam]
    exact lt_of_le_of_lt hstep1 hstep2

  have hnk : n - k - 1 ≤ (n - k - 1) * μ := by
    calc n - k - 1 = (n - k - 1) * 1 := (Nat.mul_one _).symm
      _ ≤ (n - k - 1) * μ := Nat.mul_le_mul_left _ hμ
  have hsq : n - k - 1 < k * k := lt_of_le_of_lt hnk hmul

  have hnat : n ≤ k * k + k := by
    have : n - k - 1 + 1 ≤ k * k := by omega
    omega
  have hreal : (n : ℝ) < ((k : ℝ) + 1) ^ 2 := by
    have h1 : (n : ℝ) ≤ (k : ℝ) * (k : ℝ) + (k : ℝ) := by exact_mod_cast hnat
    have h2 : (0 : ℝ) ≤ (k : ℝ) := by positivity
    nlinarith [h1, h2]

  have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  exact (Real.sqrt_lt' hpos).mpr hreal

end Qatlib.Papers.NoGlobalSym14.ParamFacts
