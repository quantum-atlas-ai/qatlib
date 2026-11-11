/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# Error probability of the final measurement

Source: R. D. Somma, S. Boixo, H. Barnum, *Quantum Simulated Annealing*,
fixed arXiv:0712.1008v1 (6 Dec 2007). Local PDF `local archive
tmp/prove/assets/0712.1008.pdf`, text twin `0712.1008.txt`.

This file covers Eq. (19), p.4, and Eq. (A19), p.6.

* Eq. (19): `P(σ ∉ S0) ≤ d e^{−βf γ} + τ' Q ν²`.  The paper's choice
  `βf = γ⁻¹ log(2d/ε²)` makes the first term `ε²/2`; together with
  `τ' Q ν² ≤ ε/2` this gives total error at most `ε`.
* Eq. (A19): combining Eq. (A4), `P ≤ √d e^{−βf γ/2} ‖h(βf)‖₂`, with
  Eq. (A18), `‖h(βf)‖₂ ≤ √2`, yields `P ≤ √(2d) e^{−βf γ/2}`.

Both are stated as pure numerical implications: the quantum-state input is the
probability bound (A4) derived from Cauchy–Schwarz in the paper.
-/

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators

namespace Qatlib.Papers.QAnnealing07.MainResults.SourceErrorBound

/-- Fixed arXiv:0712.1008v1, Eq. (19), p.4: with `βf = γ⁻¹ log(2d/ε²)` the
Boltzmann suppression factor equals `ε²/2`, i.e. `d e^{−βf γ} = ε²/2`. -/
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

/-- Fixed arXiv:0712.1008v1, Eq. (19), p.4: the two error contributions
`d e^{−βf γ}` and `τ' Q ν²` sum to at most `ε` under the paper's choice
`βf = γ⁻¹ log(2d/ε²)` and the requirement `τ' Q ν² ≤ ε/2` (with `ε ≤ 1`). -/
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

/-- Fixed arXiv:0712.1008v1, Eq. (A3)–(A4), p.5: the Cauchy–Schwarz bound
`P(σ ∉ S0) ≤ √d e^{−βf γ/2} ‖h(βf)‖₂` is improved to
`P ≤ √(2d) e^{−βf γ/2}` once `‖h(βf)‖₂² ≤ 2` (Eq. (A18)) is used. -/
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

end Qatlib.Papers.QAnnealing07.MainResults.SourceErrorBound
