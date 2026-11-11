/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# DetEstimate25 — Eq. (2): relative-error bound for the log-determinant

Fixed source: arXiv:2504.11049v2 (1 May 2025), "A quantum algorithm for
estimating the determinant", Giovannetti--Lloyd--Maccone.

This module formalizes the paper's Eq. (2) on page 2 (derivation in
Appendix C, Eqs. (C14)--(C19)).  With `alpha = log det A = n * mu` (`mu` the
mean of the log spectrum, Eq. (A2)), the total rmse of the log-determinant
decomposes as `dAlpha_err <= dAlpha_qpe + dAlpha_mc` (Eq. (C14)), with the
quantum-phase-estimation truncation `dAlpha_qpe <= 2 n kappa / 2^m` and the
Monte-Carlo term `dAlpha_mc = n Delta / sqrt(Nmc)` (Eqs. (C17), (C4)).  Hence

  `Delta alpha_err / |alpha| <= (n / |alpha|) (2 kappa / 2^m + Delta / sqrt Nmc)
                              = (1 / |mu|) (2 kappa / 2^m + Delta / sqrt Nmc)`,

and by the choices `Nmc := (2 Delta / (|mu| * eps))^2` and
`2^m = Nqpe := 4 kappa / (|mu| * eps)` the relative error is `<= eps`.

The paper keeps only the leading `2 kappa / 2^m` term of the QPE error (the
`1 / (1 - 2 kappa 2^{-m})` factor of Eq. (C19) is dropped in Eq. (2), which is
the stated headline bound).  We formalize exactly that Eq. (2) expression; the
`n/|alpha| = 1/|mu|` reduction is the algebraic identity used in the paper.

The exact source result is not present as a pre-built theorem in Frozen
v2.0.2 (searched `determinant`/`logdet`/`rmse`), so the analytic inequality is
proved here from Mathlib real-arithmetic lemmas.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.DetEstimate25.MainResults.ErrorBudget

open Real

/-- **Eq. (2), the `n / |alpha| = 1 / |mu|` reduction.**  Since `alpha = n * mu`
with `n > 0`, `n / |alpha| = 1 / |mu|`.  Source: arXiv:2504.11049v2 page 2,
Eq. (2). -/
theorem n_div_abs_alpha_eq_inv_abs_mu (n : ℕ) (α μ : ℝ)
    (hn : (0 : ℝ) < n) (hα : α = (n : ℝ) * μ) (hμ : μ ≠ 0) :
    (n : ℝ) / |α| = 1 / |μ| := by
  have hαabs : |α| = (n : ℝ) * |μ| := by
    rw [hα, abs_mul, abs_of_pos hn]
  have hμpos : 0 < |μ| := abs_pos.mpr hμ
  rw [hαabs]
  field_simp

/-- **Eq. (2), the error bound at the paper's parameter choice.**
arXiv:2504.11049v2 page 2, Eq. (2), with the substitution
`Nmc = (2 Delta / (|mu| * eps))^2` and `2^m = 4 kappa / (|mu| * eps)`:
the relative error of the log-determinant is at most `eps`.

The expression `(n / |alpha|) (2 kappa / 2^m + Delta / sqrt Nmc)` is Eq. (2);
substituting `alpha = n * mu` gives the middle form `(1/|mu|)(...)`, and the
paper's choices make both error terms equal `|mu| * eps / 2`, so the total is
`eps`. -/
theorem eq2_relative_error_bound
    (n : ℕ) (α μ κ Δ ε : ℝ)
    (hn : (0 : ℝ) < n) (hα : α = (n : ℝ) * μ)
    (hμ : μ ≠ 0) (hκ : 1 ≤ κ) (hΔ : 0 < Δ) (hε : 0 < ε) :
    ((n : ℝ) / |α|)
        * (2 * κ / (4 * κ / (|μ| * ε))
            + Δ / Real.sqrt ((2 * Δ / (|μ| * ε)) ^ 2)) ≤ ε := by
  have hκpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hμpos : 0 < |μ| := abs_pos.mpr hμ
  -- The `n/|alpha| = 1/|mu|` reduction (Eq. (2) middle form).
  rw [n_div_abs_alpha_eq_inv_abs_mu n α μ hn hα hμ]
  -- Both bracket terms equal `|mu| * eps / 2`.
  have hsqrt : Real.sqrt ((2 * Δ / (|μ| * ε)) ^ 2) = 2 * Δ / (|μ| * ε) := by
    apply Real.sqrt_sq
    positivity
  have h2m : 2 * κ / (4 * κ / (|μ| * ε)) = |μ| * ε / 2 := by
    have hκne : κ ≠ 0 := ne_of_gt hκpos
    have hμene : |μ| * ε ≠ 0 := ne_of_gt (by positivity)
    field_simp
    ring
  have hmc : Δ / (2 * Δ / (|μ| * ε)) = |μ| * ε / 2 := by
    have hΔne : Δ ≠ 0 := ne_of_gt hΔ
    have hμene : |μ| * ε ≠ 0 := ne_of_gt (by positivity)
    field_simp
  rw [hsqrt, h2m, hmc]
  have hval : (1 / |μ|) * (|μ| * ε / 2 + |μ| * ε / 2) = ε := by
    have hμne : |μ| ≠ 0 := ne_of_gt hμpos
    field_simp
    norm_num
  exact le_of_eq hval

end Qatlib.Papers.DetEstimate25.MainResults.ErrorBudget
