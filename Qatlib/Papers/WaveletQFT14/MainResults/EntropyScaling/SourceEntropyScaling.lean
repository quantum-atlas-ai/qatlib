/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# EntropyScaling — source interface for entanglement-entropy scaling

WaveletQFT14 (arXiv:1412.0750), fixed version v2 (2015-03-12).
Fixed source: https://arxiv.org/abs/1412.0750v2.

This file formalises Section V "Entanglement entropy" of the paper
(arXiv:1412.0750, p. 8–9):

* Eq. (52), the **massive** case: the Calabrese–Cardy entanglement entropy of
  the ground state, `S_A = -(1/12) log(m₀² a²) = (1/6) log(ξ/a)` with
  correlation length `ξ = 1/m₀`.
* Eq. (53), the **massless** case, where the entropy is linear in `log ℓ` for
  `ℓ ≪ L` with slope `c/3` (periodic boundaries) or `c/6` (open boundaries);
  the paper's scalar bosonic CFT has central charge `c = 1`.
* The numerical finding of Fig. 4–5: the fitted central charge is
  `c ≈ 1.004`, which agrees with `c = 1` to within `0.005`, and the same value
  is obtained when only the scaling modes (`K_ss` block of Eq. (29)) are kept.

The closed forms of Eq. (52)–(53) are proved here exactly.  The slope
extraction is formalised as the algebraic split
`S = (c/3)·log(ℓ/a) + (correction)`, which shows the log-ℓ coefficient is
`c/3`, hence the extracted central charge is `3·(c/3) = c = 1`.  The empirical
number `c = 1.004` and the agreement of the scaling-mode-only fit are
numerical observations reported by the paper; they are recorded as explicit
constants and tolerance lemmas rather than derived from a diagonalisation of
the `500`-mode covariance matrix, which is outside this paper-layer interface.

Boundary: the Gaussian covariance-matrix prescription of Eq. (54)–(57) and the
symplectic-entropy sum of Eq. (56) are the paper's computational machinery;
this file states the Calabrese–Cardy output scaling and its central-charge
content.  The von Neumann entropy `S(ρ_A) = -tr[ρ_A log ρ_A]` of Eq. (51) is the
shared `Qatlib.Foundations.QuantumEntropy.EntropyCalculus.entropy`
interface.
-/
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.WaveletQFT14.MainResults.EntropyScaling

/-- Massive-case entanglement entropy, Eq. (52): `-(1/12) log(m₀² a²)`.
(arXiv:1412.0750, Eq. (52), p. 8.) -/
def massiveEntropy (m0 a : ℝ) : ℝ := -(1 / 12) * Real.log (m0 ^ 2 * a ^ 2)

/-- Correlation length `ξ = 1/m₀` (arXiv:1412.0750, p. 8, below Eq. (52)). -/
def correlationLength (m0 : ℝ) : ℝ := 1 / m0

/-- Periodic-boundary massless entropy, Eq. (53):
`(c/3) log( (L/(π a)) · sin(π ℓ/L) ) + C_per`.
(arXiv:1412.0750, Eq. (53), p. 8.) -/
def periodicEntropy (c ℓ L a C : ℝ) : ℝ :=
  c / 3 * Real.log (L / (Real.pi * a) * Real.sin (Real.pi * ℓ / L)) + C

/-- Open-boundary massless entropy, Eq. (53):
`(c/6) log( (2L/(π a)) · sin(π ℓ/L) ) + C_open`.
(arXiv:1412.0750, Eq. (53), p. 8.) -/
def openEntropy (c ℓ L a C : ℝ) : ℝ :=
  c / 6 * Real.log (2 * L / (Real.pi * a) * Real.sin (Real.pi * ℓ / L)) + C

/-- Central charge extracted from the slope `s` of the periodic-boundary
entropy: `c = 3s` (arXiv:1412.0750, Eq. (53), p. 8). -/
def centralChargePeriodic (slope : ℝ) : ℝ := 3 * slope

/-- Central charge extracted from the slope `s` of the open-boundary entropy:
`c = 6s` (arXiv:1412.0750, Eq. (53), p. 8). -/
def centralChargeOpen (slope : ℝ) : ℝ := 6 * slope

/-- The central charge fitted from the paper's Fig. 5 numerics for the
massless scalar boson (arXiv:1412.0750, p. 8–9). -/
def measuredCentralCharge : ℝ := 1004 / 1000

/-- Eq. (52), exact identity: for `m₀, a > 0`,
`-(1/12) log(m₀² a²) = (1/6) log(ξ/a)` with `ξ = 1/m₀`.
(arXiv:1412.0750, Eq. (52), p. 8.) -/
theorem massive_entropy_eq_correlation (m0 a : ℝ) (hm : 0 < m0) (ha : 0 < a) :
    massiveEntropy m0 a = (1 / 6) * Real.log (correlationLength m0 / a) := by
  have hm0 : m0 ≠ 0 := ne_of_gt hm
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hm2 : m0 ^ 2 ≠ 0 := by positivity
  have ha2 : a ^ 2 ≠ 0 := by positivity
  have hlog : Real.log (m0 ^ 2 * a ^ 2) = 2 * Real.log m0 + 2 * Real.log a := by
    rw [Real.log_mul hm2 ha2, Real.log_pow, Real.log_pow]
    ring
  have hrlog : Real.log (correlationLength m0 / a) = -Real.log m0 - Real.log a := by
    unfold correlationLength
    rw [one_div, Real.log_div (inv_ne_zero hm0) ha0, Real.log_inv]
  unfold massiveEntropy
  rw [hlog, hrlog]
  ring

/-- Eq. (52) is positive when the correlation length exceeds the lattice
spacing, `a < ξ`: this is the physical `S_A > 0` regime.
(arXiv:1412.0750, Eq. (52), p. 8.) -/
theorem massive_entropy_pos (m0 a : ℝ) (hm : 0 < m0) (ha : 0 < a)
    (hξ : a < correlationLength m0) : 0 < massiveEntropy m0 a := by
  rw [massive_entropy_eq_correlation m0 a hm ha]
  have hratio : 1 < correlationLength m0 / a := by
    rw [one_lt_div ha]
    exact hξ
  have hlog : 0 < Real.log (correlationLength m0 / a) := Real.log_pos hratio
  linarith

/-- Eq. (53), periodic boundary, slope decomposition: the entropy splits into
the CFT term `(c/3)·log(ℓ/a)` plus a correction that depends on `ℓ` only
through the bounded factor `L·sin(πℓ/L)/(πℓ)`.  Hence the coefficient of
`log ℓ` — the slope fitted by the paper — is exactly `c/3`.
(arXiv:1412.0750, Eq. (53), p. 8.) -/
theorem periodic_entropy_decomposition (c ℓ L a C : ℝ)
    (hℓ : 0 < ℓ) (hL : 0 < L) (ha : 0 < a)
    (hsin : 0 < Real.sin (Real.pi * ℓ / L)) :
    periodicEntropy c ℓ L a C
      = c / 3 * Real.log (ℓ / a)
        + (c / 3 * Real.log (L * Real.sin (Real.pi * ℓ / L) / (Real.pi * ℓ)) + C) := by
  unfold periodicEntropy
  have hπa : 0 < Real.pi * a := by positivity
  have hπℓ : 0 < Real.pi * ℓ := mul_pos Real.pi_pos hℓ
  have hLsin : 0 < L * Real.sin (Real.pi * ℓ / L) := mul_pos hL hsin
  have harg : L / (Real.pi * a) * Real.sin (Real.pi * ℓ / L)
      = (ℓ / a) * (L * Real.sin (Real.pi * ℓ / L) / (Real.pi * ℓ)) := by
    field_simp [hℓ.ne', hL.ne', ha.ne', Real.pi_ne_zero]
  rw [harg, Real.log_mul (by positivity : ℓ / a ≠ 0)
    (div_ne_zero hLsin.ne' hπℓ.ne')]
  ring

/-- Eq. (53), open boundary, slope decomposition: the entropy splits into the
CFT term `(c/6)·log(ℓ/a)` plus a bounded correction, so the fitted slope is
`c/6`.  (arXiv:1412.0750, Eq. (53), p. 8.) -/
theorem open_entropy_decomposition (c ℓ L a C : ℝ)
    (hℓ : 0 < ℓ) (hL : 0 < L) (ha : 0 < a)
    (hsin : 0 < Real.sin (Real.pi * ℓ / L)) :
    openEntropy c ℓ L a C
      = c / 6 * Real.log (ℓ / a)
        + (c / 6 * Real.log (2 * L * Real.sin (Real.pi * ℓ / L) / (Real.pi * ℓ)) + C) := by
  unfold openEntropy
  have hπa : 0 < Real.pi * a := by positivity
  have hπℓ : 0 < Real.pi * ℓ := mul_pos Real.pi_pos hℓ
  have hLsin : 0 < 2 * L * Real.sin (Real.pi * ℓ / L) := by positivity
  have harg : 2 * L / (Real.pi * a) * Real.sin (Real.pi * ℓ / L)
      = (ℓ / a) * (2 * L * Real.sin (Real.pi * ℓ / L) / (Real.pi * ℓ)) := by
    field_simp [hℓ.ne', hL.ne', ha.ne', Real.pi_ne_zero]
  rw [harg, Real.log_mul (by positivity : ℓ / a ≠ 0)
    (div_ne_zero hLsin.ne' hπℓ.ne')]
  ring

/-- For a CFT of central charge `c = 1`, the periodic-boundary entropy of
Eq. (53) has slope `1/3`, and the extracted central charge `3·(1/3)` is `1`.
(arXiv:1412.0750, Eq. (53), p. 8.) -/
theorem periodic_central_charge_one : centralChargePeriodic ((1 : ℝ) / 3) = 1 := by
  unfold centralChargePeriodic
  norm_num

/-- For a CFT of central charge `c = 1`, the open-boundary entropy of Eq. (53)
has slope `1/6`, and the extracted central charge `6·(1/6)` is `1`.
(arXiv:1412.0750, Eq. (53), p. 8.) -/
theorem open_central_charge_one : centralChargeOpen ((1 : ℝ) / 6) = 1 := by
  unfold centralChargeOpen
  norm_num

/-- The paper's fitted value `c ≈ 1.004` agrees with the CFT value `c = 1`
within `0.005` (arXiv:1412.0750, p. 9: "We find c ≈ 1.004 which agrees with
the central charge c = 1"). -/
theorem measured_central_charge_agrees :
    |measuredCentralCharge - 1| ≤ 5 / 1000 := by
  unfold measuredCentralCharge
  norm_num

/-- The same numerical agreement when the entropy is computed keeping only the
scaling modes (`K_ss` block of Eq. (29)): a slope `s` within `5/3000` of `1/3`
yields an extracted central charge within `0.005` of `1`.
(arXiv:1412.0750, p. 9: "an accurate value is obtained by only keeping the
scaling modes".) -/
theorem scaling_modes_central_charge_accurate {slope : ℝ}
    (h : |slope - 1 / 3| ≤ 5 / 3000) :
    |centralChargePeriodic slope - 1| ≤ 5 / 1000 := by
  unfold centralChargePeriodic
  have hrewrite : 3 * slope - 1 = 3 * (slope - 1 / 3) := by ring
  rw [hrewrite, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  nlinarith [abs_nonneg (slope - 1 / 3)]

/-- Both boundary conditions reproduce the Calabrese–Cardy scaling of Eq. (53)
with the same central charge `c = 1`: the slope is `c/3` in the periodic case
and `c/6` in the open case, and both give `c = 1` when `c = 1`.
(arXiv:1412.0750, Eq. (53), p. 8.) -/
theorem eq53_central_charge_consistency :
    centralChargePeriodic ((1 : ℝ) / 3) = 1 ∧ centralChargeOpen ((1 : ℝ) / 6) = 1 :=
  ⟨periodic_central_charge_one, open_central_charge_one⟩

end Qatlib.Papers.WaveletQFT14.MainResults.EntropyScaling
