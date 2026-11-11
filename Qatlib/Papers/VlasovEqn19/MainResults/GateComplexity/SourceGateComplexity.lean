/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# GateComplexity — Eq. (46) of the Vlasov algorithm

Paper: Engel--Smith--Parker, "Quantum Algorithm for the Vlasov Equation",
fixed arXiv:1907.09418.  Claim `c004` (MainResults, p. 7).

Treating `v_max` as a constant and taking `ε = δ`, the paper's asymptotic
gate complexity (Eq. (46)) is

  `O( polylog(N_v) / δ · (t + log(1/δ) / log log(1/δ)) )`.

If `t > log(1/δ)` — true for large enough `t` and reasonable (small) `δ` —
the bracket is comparable to `t`, so the bound simplifies to

  `O( polylog(N_v) · t / δ )`.

This file formalises that simplification: with `P := polylog(N_v)` the
nonnegative polylogarithmic factor, `0 < δ`, `δ ≤ e^{-e}` (the paper's
"reasonable values of δ", ensuring `log log(1/δ) ≥ 1`) and
`log(1/δ) ≤ t`, the gate cost is at most `2 P t / δ` — the constant-factor
form of `O(polylog(N_v) t / δ)`.

Boundary: this is the pointed inequality behind the simplification, not a
full `Asymptotics.IsBigO` statement; the paper's `O` hides constants, and the
constant `2` produced here is exactly the doubling coming from
`t + log(1/δ)/log log(1/δ) ≤ 2t`.  The polylogarithmic factor is kept
symbolic as `P`; no assumption is made about how the gate synthesis is
implemented.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.VlasovEqn19.MainResults.GateComplexity

/-- The gate-complexity expression of Eq. (46) with the polylogarithmic factor
`P = polylog(N_v)`: `P/δ · (t + log(1/δ)/log log(1/δ))`. -/
def gateCost (P δ t : ℝ) : ℝ :=
  P / δ * (t + Real.log (1 / δ) / Real.log (Real.log (1 / δ)))

/-- The correction term `log(1/δ)/log log(1/δ)` never exceeds `log(1/δ)`
once `δ ≤ e^{-e}`, i.e. once `log log(1/δ) ≥ 1`. -/
theorem log_div_loglog_le_log (δ : ℝ) (hδ0 : 0 < δ)
    (hδe : δ ≤ Real.exp (-(Real.exp 1))) :
    Real.log (1 / δ) / Real.log (Real.log (1 / δ)) ≤ Real.log (1 / δ) := by
  have hlog_le : Real.log δ ≤ Real.log (Real.exp (-(Real.exp 1))) :=
    Real.log_le_log hδ0 hδe
  rw [Real.log_exp] at hlog_le
  have hL_ge : Real.exp 1 ≤ Real.log (1 / δ) := by
    have hsplit : Real.log (1 / δ) = -Real.log δ := by
      rw [Real.log_div one_ne_zero hδ0.ne']
      simp
    rw [hsplit]
    linarith
  have hL_pos : 0 < Real.log (1 / δ) := (Real.exp_pos 1).trans_le hL_ge
  have hLogL_ge : 1 ≤ Real.log (Real.log (1 / δ)) := by
    have := Real.log_le_log (Real.exp_pos 1) hL_ge
    rwa [Real.log_exp] at this
  exact div_le_self hL_pos.le hLogL_ge

/-- Claim `c004`, simplified form of Eq. (46): under `t ≥ log(1/δ)` and the
paper's reasonable-`δ` range `δ ≤ e^{-e}`, the gate complexity is at most
`2 polylog(N_v) t / δ`, i.e. `O(polylog(N_v) t / δ)` in the paper's sense. -/
theorem gate_complexity_simplifies (P δ t : ℝ) (hP : 0 ≤ P) (hδ0 : 0 < δ)
    (hδe : δ ≤ Real.exp (-(Real.exp 1))) (ht : Real.log (1 / δ) ≤ t) :
    gateCost P δ t ≤ 2 * P * t / δ := by
  have hcorr := log_div_loglog_le_log δ hδ0 hδe
  have hbracket :
      t + Real.log (1 / δ) / Real.log (Real.log (1 / δ)) ≤ 2 * t := by
    linarith
  have hcoef : 0 ≤ P / δ := div_nonneg hP hδ0.le
  have hmain : gateCost P δ t ≤ (P / δ) * (2 * t) := by
    unfold gateCost
    exact mul_le_mul_of_nonneg_left hbracket hcoef
  have heq : (P / δ) * (2 * t) = 2 * P * t / δ := by
    field_simp
  rw [heq] at hmain
  exact hmain

end Qatlib.Papers.VlasovEqn19.MainResults.GateComplexity
