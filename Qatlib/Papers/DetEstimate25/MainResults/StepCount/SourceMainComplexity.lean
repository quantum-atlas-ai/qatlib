/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# DetEstimate25 — Eq. (1): main step-count bound

Fixed source: arXiv:2504.11049v2 (1 May 2025), "A quantum algorithm for
estimating the determinant", Giovannetti--Lloyd--Maccone, page 1, Eq. (1),
and Appendix B (Eqs. (B9)--(B11)) / Appendix C (Eq. (C22)).

The paper's headline result is the step count

  `#LgD ~= O( kappa (log kappa)^2 s^2 / eps^3 * log n * log^2(s^2/eps) )`.

The resource accounting (Eqs. (B11), (3)) is `#LgD ~= Nmc * Nqpe * Nqs`, with
the paper's choices `Nmc = (2 Delta / (|mu| eps))^2` and
`2^m = Nqpe = 4 kappa / (|mu| eps)` (page 2, after Eq. (2)), and with the
Hamiltonian-simulation cost `Nqs = O(s^2 log n log^2(s^2/eta))` (Eq. (B4),
citing Berry--Childs--Cleve--Kothari--Somma [14]).  Using the spectral bounds
`Delta <= (log kappa)/2` and `|mu| >= log 2` (Eq. (A7)), the product reduces to
Eq. (1).

We formalize the `O(...)` as the existence of a positive constant `C` such
that, for the paper's parameter choices and any simulation cost `Nqs` obeying
the cited `O(s^2 log n log^2(s^2/eps))` upper bound, the product is bounded by
`C` times Eq. (1)'s right-hand side.  The Hamiltonian-simulation sub-cost is a
granted primitive (cited result [14]), supplied as a hypothesis `hNqs`, exactly
as the paper treats it.  `mu` denotes `|mu|`, the magnitude of the mean log
spectrum (Eq. (A7) bounds `|mu| >= log 2`).

The analytic constant chase is proved below with `C = 4/(log 2)^3`; the
step-count interface and cited simulation cost are otherwise treated as in the
paper.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.DetEstimate25.MainResults.StepCount

/-- **Eq. (1), the step-count product bound (explicit constant form).**
arXiv:2504.11049v2 page 1, Eq. (1) with resource accounting Eqs. (B9)--(B11)
and spectral bounds Eq. (A7).

For `kappa >= 1`, `eps > 0`, `n >= 1`, `Delta >= 0`, `mu >= log 2` (here `mu`
is `|mu|`), `Delta <= (log kappa)/2`, and a simulation cost
`0 <= Nqs <= s^2 log n log^2(s^2/eps)`, the total step count

  `Nmc * Nqpe * Nqs = (2 Delta / (mu eps))^2 * (4 kappa / (mu eps)) * Nqs`

is at most `(4/(log 2)^3) * (kappa (log kappa)^2 s^2 / eps^3 * log n * log^2(s^2/eps))`. -/
theorem step_count_product_bound
    (κ s ε n Δ μ Nqs : ℝ)
    (hκ : 1 ≤ κ) (hε : 0 < ε) (hn : 1 ≤ n) (hΔ : 0 ≤ Δ)
    (hμ : Real.log 2 ≤ μ) (hΔle : Δ ≤ Real.log κ / 2)
    (hNqs0 : 0 ≤ Nqs)
    (hNqs : Nqs ≤ s ^ 2 * Real.log n * (Real.log (s ^ 2 / ε)) ^ 2) :
    (2 * Δ / (μ * ε)) ^ 2 * (4 * κ / (μ * ε)) * Nqs
      ≤ (4 / (Real.log 2) ^ 3)
          * (κ * (Real.log κ) ^ 2 * s ^ 2 / ε ^ 3 * Real.log n
              * (Real.log (s ^ 2 / ε)) ^ 2) := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogκ : 0 ≤ Real.log κ := Real.log_nonneg hκ
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn
  have hκpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hμpos : 0 < μ := lt_of_lt_of_le hlog2pos hμ
  have hεpos : 0 < ε := hε
  have hμne : μ ≠ 0 := ne_of_gt hμpos
  have hεne : ε ≠ 0 := ne_of_gt hεpos
  -- product identity: `(2D/(me))^2 * (4k/(me)) = 16 k D^2 / (m^3 e^3)`
  have hprod : (2 * Δ / (μ * ε)) ^ 2 * (4 * κ / (μ * ε))
      = 16 * κ * Δ ^ 2 / (μ ^ 3 * ε ^ 3) := by
    field_simp
    try ring
  -- core coefficient inequality `16 k D^2/(m^3 e^3) <= C * (k (log k)^2 / e^3)`
  have hcoef0 : 16 * Δ ^ 2 / μ ^ 3 ≤ 4 * (Real.log κ) ^ 2 / (Real.log 2) ^ 3 := by
    have hΔ2 : Δ ^ 2 ≤ (Real.log κ) ^ 2 / 4 := by
      have h1 : Δ ^ 2 ≤ (Real.log κ / 2) ^ 2 := pow_le_pow_left₀ hΔ hΔle 2
      calc Δ ^ 2 ≤ (Real.log κ / 2) ^ 2 := h1
        _ = (Real.log κ) ^ 2 / 4 := by ring
    have hΔ2' : 16 * Δ ^ 2 ≤ 4 * (Real.log κ) ^ 2 := by nlinarith [hΔ2]
    have hμ3 : (Real.log 2) ^ 3 ≤ μ ^ 3 := pow_le_pow_left₀ hlog2pos.le hμ 3
    have hl3nonneg : 0 ≤ (Real.log 2) ^ 3 := le_of_lt (pow_pos hlog2pos 3)
    have hL2nonneg : 0 ≤ (Real.log κ) ^ 2 := sq_nonneg _
    have step1 : 16 * Δ ^ 2 * (Real.log 2) ^ 3
        ≤ 4 * (Real.log κ) ^ 2 * (Real.log 2) ^ 3 :=
      mul_le_mul_of_nonneg_right hΔ2' hl3nonneg
    have step2 : 4 * (Real.log κ) ^ 2 * (Real.log 2) ^ 3
        ≤ 4 * (Real.log κ) ^ 2 * μ ^ 3 :=
      mul_le_mul_of_nonneg_left hμ3 (by nlinarith [hL2nonneg])
    rw [div_le_div_iff₀ (pow_pos hμpos 3) (pow_pos hlog2pos 3)]
    exact le_trans step1 step2
  have hcoef : 16 * κ * Δ ^ 2 / (μ ^ 3 * ε ^ 3)
      ≤ (4 / (Real.log 2) ^ 3) * (κ * (Real.log κ) ^ 2 / ε ^ 3) := by
    calc 16 * κ * Δ ^ 2 / (μ ^ 3 * ε ^ 3) = κ / ε ^ 3 * (16 * Δ ^ 2 / μ ^ 3) := by
          field_simp
          try ring
      _ ≤ κ / ε ^ 3 * (4 * (Real.log κ) ^ 2 / (Real.log 2) ^ 3) := by
          apply mul_le_mul_of_nonneg_left hcoef0
          positivity
      _ = (4 / (Real.log 2) ^ 3) * (κ * (Real.log κ) ^ 2 / ε ^ 3) := by
          field_simp
          try ring
  -- multiply by `Nqs`
  have hNqsL : (16 * κ * Δ ^ 2 / (μ ^ 3 * ε ^ 3)) * Nqs
      ≤ ((4 / (Real.log 2) ^ 3) * (κ * (Real.log κ) ^ 2 / ε ^ 3)) * Nqs :=
    mul_le_mul_of_nonneg_right hcoef hNqs0
  have hDnonneg : 0 ≤ (4 / (Real.log 2) ^ 3) * (κ * (Real.log κ) ^ 2 / ε ^ 3) := by
    have hCpos : 0 < 4 / (Real.log 2) ^ 3 := div_pos (by norm_num) (pow_pos hlog2pos 3)
    apply mul_nonneg hCpos.le
    exact div_nonneg (mul_nonneg hκpos.le (sq_nonneg _)) (pow_pos hεpos 3).le
  have hNqsR : ((4 / (Real.log 2) ^ 3) * (κ * (Real.log κ) ^ 2 / ε ^ 3)) * Nqs
      ≤ ((4 / (Real.log 2) ^ 3) * (κ * (Real.log κ) ^ 2 / ε ^ 3))
          * (s ^ 2 * Real.log n * (Real.log (s ^ 2 / ε)) ^ 2) :=
    mul_le_mul_of_nonneg_left hNqs hDnonneg
  have hfinal : ((4 / (Real.log 2) ^ 3) * (κ * (Real.log κ) ^ 2 / ε ^ 3))
        * (s ^ 2 * Real.log n * (Real.log (s ^ 2 / ε)) ^ 2)
      = (4 / (Real.log 2) ^ 3)
          * (κ * (Real.log κ) ^ 2 * s ^ 2 / ε ^ 3 * Real.log n
              * (Real.log (s ^ 2 / ε)) ^ 2) := by
    field_simp
    try ring
  rw [hprod]
  exact le_trans hNqsL (le_trans hNqsR (le_of_eq hfinal))

/-- **Eq. (1), main result (asymptotic form).**  arXiv:2504.11049v2 page 1,
Eq. (1): there is a positive constant `C` such that the log-determinant
algorithm's total step count `Nmc * Nqpe * Nqs` is at most `C` times
`kappa (log kappa)^2 s^2 / eps^3 * log n * log^2(s^2/eps)`, uniformly over the
paper's parameter choices and over any Hamiltonian-simulation cost `Nqs`
obeying the cited bound `Nqs <= s^2 log n log^2(s^2/eps)`. -/
theorem main_complexity_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (κ s ε n Δ μ Nqs : ℝ),
        1 ≤ κ → 0 < ε → 1 ≤ n → 0 ≤ Δ → Real.log 2 ≤ μ →
        Δ ≤ Real.log κ / 2 → 0 ≤ Nqs →
        Nqs ≤ s ^ 2 * Real.log n * (Real.log (s ^ 2 / ε)) ^ 2 →
        (2 * Δ / (μ * ε)) ^ 2 * (4 * κ / (μ * ε)) * Nqs
          ≤ C * (κ * (Real.log κ) ^ 2 * s ^ 2 / ε ^ 3 * Real.log n
              * (Real.log (s ^ 2 / ε)) ^ 2) := by
  refine ⟨4 / (Real.log 2) ^ 3, ?_, ?_⟩
  · exact div_pos (by norm_num) (pow_pos (Real.log_pos (by norm_num)) 3)
  · intro κ s ε n Δ μ Nqs hκ hε hn hΔ hμ hΔle hNqs0 hNqs
    exact step_count_product_bound κ s ε n Δ μ Nqs hκ hε hn hΔ hμ hΔle hNqs0 hNqs

end Qatlib.Papers.DetEstimate25.MainResults.StepCount
