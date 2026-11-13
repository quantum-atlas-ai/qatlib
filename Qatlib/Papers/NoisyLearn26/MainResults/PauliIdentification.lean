/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NoisyLearn26.MainResults.Models.InterfaceModels

/-!
# Scalar bounds for noisy Pauli identification

Defines the expressions `nscLower` and `ntcUpper` and relates them through
`corollary27Exponent`. The results establish positivity of the noise polynomial, an upper bound
on the exponent, and elementary size and zero-noise identities. See [CotlerGongKannan2025] for
the surrounding analysis.

## Main statements

* `corollary27_exponent_identity`: For positive `n` and `0 < lam < 1`, raising `ntcUpper n lam`
  to `corollary27Exponent n lam` yields `nscLower n lam`.
* `corollary27_exponent_le_inv_lambda`: For `n ≥ 1` and `0 < lam ≤ 1 / 2`, the exponent
  `corollary27Exponent n lam` is at most `log 4 / (4 * lam)`.
* `nsc_exponential_in_n`: For `lam` in `[0, 1]`, the expression `nscLower n lam` is at least
  `2^n`.

## References

* [Cotler et al., 2025][CotlerGongKannan2025]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NoisyLearn26.MainResults.PauliIdentification

open Qatlib.Papers.NoisyLearn26.MainResults

/-- The single-copy lower-bound expression `(2 / fLambda lam) ^ (n : ℝ)`. -/
def nscLower (n : ℕ) (lam : ℝ) : ℝ := (2 / fLambda lam) ^ (n : ℝ)

/-- The two-copy upper-bound expression `twoCopySampleCost n lam`. -/
def ntcUpper (n : ℕ) (lam : ℝ) : ℝ := (n : ℝ) * (1 - lam) ^ (-(4 * (n : ℝ)))

/-- The noise polynomial `fLambda lam` is positive for `lam` in `[0, 1]`. -/
theorem fLambda_pos {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) : 0 < fLambda lam := by
  unfold fLambda
  nlinarith [sq_nonneg (lam - 1)]

/-- The noise polynomial `fLambda lam` is at least `1 / 2` for `lam` in `[0, 1]`. -/
theorem half_le_fLambda {lam : ℝ} (_h0 : 0 ≤ lam) (_h1 : lam ≤ 1) :
    (1 : ℝ) / 2 ≤ fLambda lam := by
  unfold fLambda
  nlinarith [sq_nonneg (lam - 1)]

/-- For positive `n` and `0 < lam < 1`, raising `ntcUpper n lam` to `corollary27Exponent n lam`
yields `nscLower n lam` [CotlerGongKannan2025]. -/
theorem corollary27_exponent_identity {n : ℕ} (hn : 0 < n) {lam : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    ntcUpper n lam ^ corollary27Exponent n lam = nscLower n lam := by
  have hNpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h1lam : (0 : ℝ) < 1 - lam := by linarith
  have hFpos : (0 : ℝ) < fLambda lam := fLambda_pos (le_of_lt hlam0) (le_of_lt hlam1)
  have hbase : (0 : ℝ) < ntcUpper n lam := by
    unfold ntcUpper
    exact mul_pos hNpos (Real.rpow_pos_of_pos h1lam _)
  have hlog1 : Real.log (1 - lam) < 0 := Real.log_neg h1lam (by linarith)
  have hlogN : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hden : Real.log (n : ℝ) - 4 * (n : ℝ) * Real.log (1 - lam) ≠ 0 := by
    have : 0 < Real.log (n : ℝ) - 4 * (n : ℝ) * Real.log (1 - lam) := by
      nlinarith
    exact ne_of_gt this

  have hlogNTC : Real.log (ntcUpper n lam) =
      Real.log (n : ℝ) - 4 * (n : ℝ) * Real.log (1 - lam) := by
    unfold ntcUpper
    rw [Real.log_mul (ne_of_gt hNpos) (ne_of_gt (Real.rpow_pos_of_pos h1lam _))]
    rw [Real.log_rpow h1lam]
    ring

  have hcancel : (Real.log (n : ℝ) - 4 * (n : ℝ) * Real.log (1 - lam)) *
        corollary27Exponent n lam = Real.log (2 / fLambda lam) * (n : ℝ) := by
    unfold corollary27Exponent
    rw [mul_comm (Real.log (n : ℝ) - 4 * (n : ℝ) * Real.log (1 - lam))]
    rw [div_mul_eq_mul_div, mul_div_cancel_right₀ _ hden]
    ring
  rw [Real.rpow_def_of_pos hbase, hlogNTC, hcancel, nscLower,
    Real.rpow_def_of_pos (by positivity : (0:ℝ) < 2 / fLambda lam)]

/-- For `n ≥ 1` and `0 < lam ≤ 1 / 2`, the exponent `corollary27Exponent n lam` is at most `log
4 / (4 * lam)` [CotlerGongKannan2025]. -/
theorem corollary27_exponent_le_inv_lambda {n : ℕ} (hn : 1 ≤ n) {lam : ℝ}
    (hlam0 : 0 < lam) (hlamh : lam ≤ 1 / 2) :
    corollary27Exponent n lam ≤ Real.log 4 / (4 * lam) := by
  have hNpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h1lam : (0 : ℝ) < 1 - lam := by linarith
  have hFpos : (0 : ℝ) < fLambda lam := fLambda_pos (le_of_lt hlam0) (by linarith)
  have hhalf : (1 : ℝ) / 2 ≤ fLambda lam := half_le_fLambda (le_of_lt hlam0) (by linarith)
  have hlog1 : Real.log (1 - lam) < 0 := Real.log_neg h1lam (by linarith)
  have hlogN : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hdenpos : 0 < Real.log (n : ℝ) - 4 * (n : ℝ) * Real.log (1 - lam) := by
    nlinarith
  have h2f_pos : (0 : ℝ) < 2 / fLambda lam := by positivity
  have h2f4 : 2 / fLambda lam ≤ 4 := by
    rw [div_le_iff₀ hFpos]
    nlinarith
  have hlog2f : Real.log (2 / fLambda lam) ≤ Real.log 4 :=
    Real.log_le_log h2f_pos h2f4
  have hlog4pos : 0 < Real.log 4 := Real.log_pos (by norm_num)

  have hneglog : lam ≤ -Real.log (1 - lam) := by
    have := Real.log_le_sub_one_of_pos h1lam
    linarith
  rw [corollary27Exponent]
  rw [div_le_iff₀ hdenpos]
  have hstep : (n : ℝ) * Real.log (2 / fLambda lam) ≤ (n : ℝ) * Real.log 4 := by
    have := mul_le_mul_of_nonneg_left hlog2f (le_of_lt hNpos)
    exact this
  have hsecond : (n : ℝ) * Real.log 4 ≤
      Real.log 4 / (4 * lam) * (4 * (n : ℝ) * (-Real.log (1 - lam))) := by
    have hlamne : lam ≠ 0 := ne_of_gt hlam0
    have hlog4nonneg : 0 ≤ Real.log 4 := le_of_lt hlog4pos
    rw [div_mul_eq_mul_div]

    rw [le_div_iff₀ (by positivity : (0:ℝ) < 4 * lam)]
    nlinarith [mul_nonneg (le_of_lt hNpos) hlog4nonneg,
      mul_nonneg (mul_nonneg (le_of_lt hNpos) hlog4nonneg) (sub_nonneg.mpr hneglog)]
  have hmain : (n : ℝ) * Real.log (2 / fLambda lam) ≤
      Real.log 4 / (4 * lam) * (Real.log (n : ℝ) - 4 * (n : ℝ) * Real.log (1 - lam)) := by
    have hsplit : Real.log 4 / (4 * lam) *
        (Real.log (n : ℝ) - 4 * (n : ℝ) * Real.log (1 - lam)) =
        Real.log 4 / (4 * lam) * Real.log (n : ℝ) +
        Real.log 4 / (4 * lam) * (4 * (n : ℝ) * (-Real.log (1 - lam))) := by ring
    rw [hsplit]
    have hfirst : 0 ≤ Real.log 4 / (4 * lam) * Real.log (n : ℝ) := by positivity
    linarith
  exact hmain

/-- For `lam` in `[0, 1]`, the expression `nscLower n lam` is at least `2^n`
[CotlerGongKannan2025]. -/
theorem nsc_exponential_in_n {n : ℕ} {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    (2 : ℝ) ^ (n : ℝ) ≤ nscLower n lam := by
  unfold nscLower
  have hFpos : 0 < fLambda lam := fLambda_pos h0 h1
  have hFle : fLambda lam ≤ 1 := by
    unfold fLambda
    nlinarith [sq_nonneg lam]
  have hbase : (2 : ℝ) ≤ 2 / fLambda lam := by
    rw [le_div_iff₀ hFpos]
    nlinarith
  exact Real.rpow_le_rpow (by norm_num) hbase (by positivity)

/-- At zero noise, `ntcUpper n 0` equals `n` [CotlerGongKannan2025]. -/
theorem ntc_at_zero_noise (n : ℕ) : ntcUpper n 0 = (n : ℝ) := by
  unfold ntcUpper
  simp

end Qatlib.Papers.NoisyLearn26.MainResults.PauliIdentification
