/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabaticQLS21.MainResults.Setup.OperatorModel
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

set_option backward.isDefEq.respectTransparency false

/-!
# Linear Condition-Number Query Scaling for Adiabatic QLSP

This module establishes the oracle-call scaling of Theorem 19: combining a fixed-precision
discrete adiabatic evolution phase of cost `O(κ)` with a finite-precision eigenstate
filtering phase of cost `O(κ log(2 / ε))` yields a total cost bounded by `O(κ log(1 / ε))`
for `0 < ε ≤ 1 / 2`.

## Main statements

* `source_theorem19`: linear-`κ`, logarithmic-precision total query bound `C' * κ * log(1 / ε)`.

## References

* [Costa et al., 2022][CostaEtAl2022], Theorem 19, Eq. (162), p. 23.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.AdiabaticQLS21.MainResults.Qlsp

open Qatlib.Papers.AdiabaticQLS21.MainResults.Setup

/-- **Theorem 19**: when the fixed-precision adiabatic phase uses at most `C * κ` oracle
calls and the eigenstate filtering phase uses at most `C * κ * log(2 / ε)` oracle calls,
their combined cost satisfies `callsA + callsF ε ≤ C' * κ * log(1 / ε)` for `0 < ε ≤ 1 / 2`. -/
theorem source_theorem19
    (κ : ℝ) (hκ : 1 < κ) (callsA : ℝ) (callsF : ℝ → ℝ) (C : ℝ)
    (hC : 0 < C)
    (hAdia : callsA ≤ C * κ)
    (hFilter : ∀ ε : ℝ, 0 < ε → callsF ε ≤ C * κ * Real.log (2 / ε)) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      callsA + callsF ε ≤ C' * κ * Real.log (1 / ε) := by
  have hκ0 : (0 : ℝ) < κ := by linarith
  have hCk : 0 ≤ C * κ := mul_nonneg hC.le hκ0.le
  refine ⟨4 * C, by positivity, ?_⟩
  intro ε hε hεhalf
  have h2ε : (2 : ℝ) ≤ 1 / ε := by
    rw [le_div_iff₀ hε]
    linarith
  have hlogge : Real.log 2 ≤ Real.log (1 / ε) :=
    Real.log_le_log (by norm_num) h2ε
  have hlogmul : Real.log (2 / ε) = Real.log 2 + Real.log (1 / ε) := by
    rw [show (2 : ℝ) / ε = 2 * (1 / ε) by ring]
    exact Real.log_mul (by norm_num) (by
      have h : (0 : ℝ) < 1 / ε := by positivity
      exact h.ne')
  have hlog2half : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hL1 : (1 : ℝ) ≤ 2 * Real.log (1 / ε) := by linarith
  have hFbound : callsF ε ≤ C * κ * (2 * Real.log (1 / ε)) := by
    have h1 : Real.log (2 / ε) ≤ 2 * Real.log (1 / ε) := by
      rw [hlogmul]
      linarith
    exact (hFilter ε hε).trans (mul_le_mul_of_nonneg_left h1 hCk)
  have hAbound : callsA ≤ C * κ * (2 * Real.log (1 / ε)) := by
    calc callsA ≤ C * κ := hAdia
      _ = C * κ * 1 := (mul_one _).symm
      _ ≤ C * κ * (2 * Real.log (1 / ε)) :=
          mul_le_mul_of_nonneg_left hL1 hCk
  calc callsA + callsF ε
      ≤ C * κ * (2 * Real.log (1 / ε)) + C * κ * (2 * Real.log (1 / ε)) :=
        add_le_add hAbound hFbound
    _ = 4 * C * κ * Real.log (1 / ε) := by ring

end Qatlib.Papers.AdiabaticQLS21.MainResults.Qlsp
