/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Arithmetic of the high-probability query cap

Berry--Cleve--Somma, "Exponential improvement in precision for Hamiltonian-evolution
simulation", fixed arXiv:1308.5424v3, Appendix A1, Eqs. (14)--(17).

The appendix bounds the number of segment attempts needed to complete `T` segments.
With success probability at least `3/4` per attempt, and `X` the number of successes
among `N = 2T + λ` attempts, failure to reach `T` implies `X < (1 - δ) μ` with
`δ = λ / (6T + 3λ)` and `μ = (3/2)T + (3/4)λ` (Eq. (15)). Substituting this `δ` into
the Chernoff bound `Pr[X < (1-δ)μ] < exp(-δ²μ/2)` (Eq. (16)) gives the exponent

    exp(-λ² / (24 (2T + λ)))                                            (Eq. (17)).

This file isolates the *deterministic* algebraic skeleton of that step: the exponent
identity Eq. (17), and the explicit choice `λ = 24 (2T + log(1/ε))` that makes the
failure exponent at least `log(1/ε)`, so the cap `N = 2T + λ` is `O(T + log(1/ε))`
as in Eq. (14). The Chernoff bound itself (Eq. (16)) is a standard probabilistic
input and is not reproved here.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HamEvoPrec13.QueryCap

/-- The algebraic identity behind Eq. (17): with the paper's deviation
`δ = λ / (6T + 3λ)` and mean lower bound `μ = (3/2)T + (3/4)λ`, the Chernoff exponent
`δ² μ / 2` equals `λ² / (24 (2T + λ))`. -/
theorem chernoff_exponent_identity (T lam : ℝ) (hT : 0 ≤ T) (hlam : 0 < lam) :
    (lam / (6 * T + 3 * lam)) ^ 2 * ((3 / 2 : ℝ) * T + (3 / 4 : ℝ) * lam) / 2
      = lam ^ 2 / (24 * (2 * T + lam)) := by
  have h1 : (6 * T + 3 * lam) ≠ 0 := by positivity
  have h2 : (2 * T + lam) ≠ 0 := by positivity
  have h3 : ((3 / 2 : ℝ) * T + (3 / 4 : ℝ) * lam) = (3 / 4) * (2 * T + lam) := by ring
  rw [h3]
  field_simp
  ring

/-- The cap `N = 2T + λ` with `λ = 24 (2T + L)` gives failure exponent at least `L`:
`λ² / (24 (2T + λ)) ≥ L`. This is the inequality that turns Eq. (17) into Eq. (14). -/
theorem cap_exponent_ge (T L : ℝ) (hT : 0 ≤ T) (hL : 0 ≤ L) (hTL : 0 < 2 * T + L) :
    L ≤ (24 * (2 * T + L)) ^ 2 / (24 * (2 * T + 24 * (2 * T + L))) := by
  have hden : 0 < 24 * (2 * T + 24 * (2 * T + L)) := by positivity
  rw [le_div_iff₀ hden]
  nlinarith [sq_nonneg T, mul_nonneg hT hL, sq_nonneg (2 * T + L)]

/-- Consequently the Chernoff failure probability with the explicit cap is at most
`exp(-L)`, i.e. at most `ε` when `L = log(1/ε)`. -/
theorem cap_failure_prob_le (T L : ℝ) (hT : 0 ≤ T) (hL : 0 ≤ L) (hTL : 0 < 2 * T + L) :
    Real.exp (-((24 * (2 * T + L)) ^ 2 / (24 * (2 * T + 24 * (2 * T + L)))))
      ≤ Real.exp (-L) := by
  apply Real.exp_le_exp.mpr
  have h := cap_exponent_ge T L hT hL hTL
  linarith

/-- The explicit cap `2T + 24(2T + L)` is `O(T + L)` with the concrete constant `50`:
`2T + 24(2T + L) ≤ 50 (T + L)`. This is the `N = O(T + log(1/ε))` of Eq. (14). -/
theorem cap_linear_bound (T L : ℝ) (hL : 0 ≤ L) :
    2 * T + 24 * (2 * T + L) ≤ 50 * (T + L) := by
  nlinarith

end Qatlib.Papers.HamEvoPrec13.QueryCap
