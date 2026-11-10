/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.GraphModelMath.SrgQuotient.Defs
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

set_option autoImplicit false

namespace Qatlib.Papers.NoGlobalSym14.ParamFacts

open SimpleGraph

theorem source_param_identity {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {n k ℓ μ : ℕ} (h : G.IsSRGWith n k ℓ μ) (hn : 0 < n) :
    k * (k - ℓ - 1) = (n - k - 1) * μ :=
  Qatlib.Foundations.GraphModelMath.SrgQuotient.parameter_identity G h hn

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
