/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# DetEstimate25 — Eq. (4): relative-error bound for general spectral sums

Fixed source: arXiv:2504.11049v2 (1 May 2025), "A quantum algorithm for
estimating the determinant", Giovannetti--Lloyd--Maccone, page 2, Eq. (4).

For an arbitrary readily-computable non-negative `f`, the paper replaces
Eq. (2) by the bound

  `Delta F_err / |F| ≈ (1 / mu_f) ( sum_j |fdot(lambda_j)| / (2^m n) + Delta_f / sqrt Nmc )
                    <= (1 / mu_f) ( |fdot|_max / 2^m + Delta_f / sqrt Nmc )`,

where `mu_f = (1/n) sum_j f(lambda_j) > 0`, `Delta_f` is the variance of `f`
on the spectrum, `fdot = df/dx`, and `|fdot|_max` is the maximum magnitude of
`fdot` over the eigenvalue range.

The only analytic content of the second inequality is `sum_j |fdot(lambda_j)|`
`/ (2^m n) <= |fdot|_max / 2^m`, i.e. a finite sum bounded by `n` times a
pointwise maximum.  We formalize exactly this: for any `fdot : Fin n -> R` and
any pointwise upper bound `M` (`M` plays `|fdot|_max`), the normalized sum is
at most `M / q` where `q = 2^m`, and then the full `(1/mu_f)`-scaled bound
follows by monotonicity of multiplication by the positive `1/mu_f`.

The finite-sum inequality is proved here from Mathlib; the heuristic
identification preceding the inequality remains part of the paper-level scope.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.DetEstimate25.MainResults.SpectralSum

open Finset

/-- **Finite-sum maximum bound.**  The sum of `|f` over the `n`-point
spectrum is at most `n` times a pointwise upper bound `M`.  Source context:
arXiv:2504.11049v2 Eq. (4), the step turning `sum_j |fdot(lambda_j)| / n` into
`|fdot|_max`. -/
theorem sum_abs_le_card_mul {n : ℕ} (f : Fin n → ℝ) (M : ℝ)
    (hM : ∀ j, |f j| ≤ M) :
    (∑ j : Fin n, |f j|) ≤ (n : ℝ) * M := by
  calc ∑ j : Fin n, |f j| ≤ ∑ _j : Fin n, M := Finset.sum_le_sum (fun j _ => hM j)
    _ = (n : ℝ) * M := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Eq. (4), the spectral-sum relative-error bound.**
arXiv:2504.11049v2 page 2, Eq. (4).  For `fdot : Fin n -> R` a pointwise
bound `M` on `|fdot(lambda_j)|`, positive spectral mean `mu_f`, and `q = 2^m
> 0`,

  `(1/mu_f) ( (sum_j |fdot j|) / (q n) + Delta_f / sqrt Nmc )
     <= (1/mu_f) ( M / q + Delta_f / sqrt Nmc )`.

The first factor of the paper's displayed chain (the `≈` relating
`Delta F_err/|F|` to the ensemble average) is heuristic; the rigorous
inequality content is the `<=` proved here, matching the paper's `<=` step. -/
theorem eq4_spectral_sum_bound
    (n : ℕ) (hn : 0 < n)
    (fdot : Fin n → ℝ) (M μf Δf q Nmc : ℝ)
    (hM : ∀ j, |fdot j| ≤ M)
    (hμf : 0 < μf) (hq : 0 < q) :
    (1 / μf) * ((∑ j : Fin n, |fdot j|) / (q * (n : ℝ)) + Δf / Real.sqrt Nmc)
      ≤ (1 / μf) * (M / q + Δf / Real.sqrt Nmc) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < q * (n : ℝ) := mul_pos hq hnpos
  -- finite-sum vs maximum
  have hsum : (∑ j : Fin n, |fdot j|) ≤ (n : ℝ) * M := sum_abs_le_card_mul fdot M hM
  have hstep : (∑ j : Fin n, |fdot j|) / (q * (n : ℝ)) ≤ M / q := by
    have h1 : (∑ j : Fin n, |fdot j|) / (q * (n : ℝ))
        ≤ ((n : ℝ) * M) / (q * (n : ℝ)) :=
      div_le_div_of_nonneg_right hsum (le_of_lt hden)
    have heq : ((n : ℝ) * M) / (q * (n : ℝ)) = M / q := by
      have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
      have hqne : q ≠ 0 := ne_of_gt hq
      field_simp
    rw [heq] at h1
    exact h1
  have hinner :
      (∑ j : Fin n, |fdot j|) / (q * (n : ℝ)) + Δf / Real.sqrt Nmc
        ≤ M / q + Δf / Real.sqrt Nmc := by
    linarith [hstep]
  exact mul_le_mul_of_nonneg_left hinner (le_of_lt (one_div_pos.mpr hμf))

end Qatlib.Papers.DetEstimate25.MainResults.SpectralSum
