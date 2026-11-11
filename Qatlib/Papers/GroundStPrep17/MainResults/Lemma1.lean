/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GroundStPrep17.MainResults.CostLedger
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 1 of arXiv:1712.03193v2 (fixed version v2, 2 Feb 2018)

*No-overshoot and small-overturn bounds for fixed-point search* (p. 9).

For `C` preparing `√λ |T⟩ + √(1-λ²) |T̄⟩` and `U` marking `T`, the fixed point
search `FPS(C, U, λ', δ)` on `n' + 1` qubits uses `O(log(1/δ)/λ')` calls to
`C, C†, U` and satisfies

* (i)  if `λ ≥ λ'`, then `|⟨T,0|FPS(C,U,λ',δ)|0⟩^{⊗(n'+1)}|² ≥ 1 - δ²`;
* (ii) if `λ ≤ λ'`, then `|⟨T,0|FPS(C,U,λ',δ)|0⟩^{⊗(n'+1)}| ≤ 2(λ/λ') ln(2/δ)`.

The success probability is formalised by the paper's own Chebyshev formula,
eq. (33):

`P = 1 - (δ · T_t(τ √(1-λ²)))²`,  `τ = T_{1/t}(1/δ) = cosh(arcosh(1/δ)/t)`,
with `t` the number of calls.  Part (i) is proved from this formula, taking as
hypothesis the regime condition `|T_t(τ √(1-λ²))| ≤ 1` (the non-overshoot
content of [24] for `λ ≥ λ'`).  Part (ii) takes as hypothesis the mean-value
bound `P ≤ 2 t (t+1) λ²` of eqs. (34)-(39) (the Chebyshev derivative /
monotonicity argument) and derives the displayed `2(λ/λ')ln(2/δ)` amplitude
bound from the call count `t`.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.GroundStPrep17.MainResults.LemmaOne

open Qatlib.Papers.GroundStPrep17.MainResults

/-- `τ = T_{1/t}(1/δ) = cosh(arcosh(1/δ)/t)`, eqs. (33)-(34). -/
def fpsTau (δ : ℝ) (t : ℕ) : ℝ := Real.cosh (Real.arcosh (1 / δ) / (t : ℝ))

/-- `T_t(τ) = 1/δ`, the normalisation used in eq. (34). -/
lemma fpsTau_chebyshev {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {t : ℕ} (ht : t ≠ 0) :
    (Polynomial.Chebyshev.T ℝ (t : ℤ)).eval (fpsTau δ t) = 1 / δ := by
  have h1δ : 1 ≤ 1 / δ := by
    rw [le_div_iff₀ hδ0]
    simpa using hδ1
  unfold fpsTau
  rw [Polynomial.Chebyshev.T_real_cosh]
  have htR : (t : ℝ) ≠ 0 := by exact_mod_cast ht
  have harg : ((t : ℤ) : ℝ) * (Real.arcosh (1 / δ) / (t : ℝ)) = Real.arcosh (1 / δ) := by
    push_cast
    field_simp [htR]
  rw [harg, Real.cosh_arcosh h1δ]

/-- The fixed-point-search success probability, eq. (33):
`P = 1 - (δ · T_t(τ √(1-λ²)))²`. -/
def fpsSuccessProbability (lam δ : ℝ) (t : ℕ) : ℝ :=
  1 - (δ * (Polynomial.Chebyshev.T ℝ (t : ℤ)).eval
    (fpsTau δ t * Real.sqrt (1 - lam ^ 2))) ^ 2

/-- **Lemma 1(i)**: if `λ' ≤ λ ≤ 1` and the Chebyshev argument satisfies
`|T_t(τ√(1-λ²))| ≤ 1` (no overshoot), then `P ≥ 1 - δ²`. -/
theorem lemma1_no_overshoot {lam lam' δ : ℝ} {t : ℕ}
    (_hlam'0 : 0 ≤ lam') (_hlamlam' : lam' ≤ lam) (_hlam1 : lam ≤ 1)
    (_hδ0 : 0 < δ) (_hδ1 : δ ≤ 1) (_ht : t ≠ 0)
    (hreg : |(Polynomial.Chebyshev.T ℝ (t : ℤ)).eval
      (fpsTau δ t * Real.sqrt (1 - lam ^ 2))| ≤ 1) :
    1 - δ ^ 2 ≤ fpsSuccessProbability lam δ t := by
  unfold fpsSuccessProbability
  have hT2 : (Polynomial.Chebyshev.T ℝ (t : ℤ)).eval
      (fpsTau δ t * Real.sqrt (1 - lam ^ 2)) ^ 2 ≤ 1 :=
    (sq_le_one_iff_abs_le_one _).mpr hreg
  have hsq : (δ * (Polynomial.Chebyshev.T ℝ (t : ℤ)).eval
      (fpsTau δ t * Real.sqrt (1 - lam ^ 2))) ^ 2 ≤ δ ^ 2 := by
    rw [mul_pow]
    calc δ ^ 2 * (Polynomial.Chebyshev.T ℝ (t : ℤ)).eval
          (fpsTau δ t * Real.sqrt (1 - lam ^ 2)) ^ 2
        ≤ δ ^ 2 * 1 := mul_le_mul_of_nonneg_left hT2 (sq_nonneg δ)
      _ = δ ^ 2 := by ring
  linarith [hsq]

/-- The mean-value bound of eqs. (34)-(39): `P ≤ 2 t (t+1) λ²`. -/
def fpsMeanValueBound (lam δ : ℝ) (t : ℕ) : Prop :=
  fpsSuccessProbability lam δ t ≤ 2 * (t : ℝ) * ((t : ℝ) + 1) * lam ^ 2

/-- **Lemma 1(ii)**: if `λ ≤ λ'`, the search uses `t` calls with
`t λ' ≤ log(2/δ)`, and the Chebyshev mean-value bound holds, then the amplitude
is at most `2(λ/λ') log(2/δ)`. -/
theorem lemma1_small_amplitude {lam lam' δ : ℝ} {t : ℕ}
    (hlam'0 : 0 < lam') (_hlamlam' : lam ≤ lam') (hlam : 0 ≤ lam) (hδ0 : 0 < δ) (_hδ1 : δ < 1)
    (ht1 : 1 ≤ t) (htL : (t : ℝ) * lam' ≤ Real.log (2 / δ))
    (hmean : fpsMeanValueBound lam δ t) :
    Real.sqrt (fpsSuccessProbability lam δ t) ≤ 2 * (lam / lam') * Real.log (2 / δ) := by
  have hL0 : 0 < Real.log (2 / δ) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hδ0]
    linarith
  have ht0 : (0 : ℝ) < (t : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ht1)
  have htpos : (0 : ℝ) ≤ (t : ℝ) := ht0.le
  have hR0 : 0 ≤ 2 * (lam / lam') * Real.log (2 / δ) := by
    have hdiv : 0 ≤ lam / lam' := div_nonneg hlam hlam'0.le
    positivity
  have hlam'2 : 0 < lam' ^ 2 := by positivity
  have hkey : 2 * (t : ℝ) * ((t : ℝ) + 1) * lam ^ 2
      ≤ (2 * (lam / lam') * Real.log (2 / δ)) ^ 2 := by
    have ht1' : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht1
    have h1 : (t : ℝ) + 1 ≤ 2 * (t : ℝ) := by linarith
    have htprod : (t : ℝ) * ((t : ℝ) + 1) ≤ 2 * (t : ℝ) ^ 2 := by
      calc (t : ℝ) * ((t : ℝ) + 1) ≤ (t : ℝ) * (2 * (t : ℝ)) :=
            mul_le_mul_of_nonneg_left h1 htpos
        _ = 2 * (t : ℝ) ^ 2 := by ring
    have htlam'0 : 0 ≤ (t : ℝ) * lam' := mul_nonneg htpos hlam'0.le
    have htL2 : ((t : ℝ) * lam') ^ 2 ≤ Real.log (2 / δ) ^ 2 :=
      sq_le_sq' (by nlinarith [htlam'0, hL0]) htL
    have hsq : (t : ℝ) ^ 2 * lam' ^ 2 ≤ Real.log (2 / δ) ^ 2 := by
      have h := htL2
      rwa [mul_pow] at h
    have hrhs : (2 * (lam / lam') * Real.log (2 / δ)) ^ 2
        = 4 * lam ^ 2 * Real.log (2 / δ) ^ 2 / lam' ^ 2 := by
      field_simp [hlam'0.ne']
      ring
    rw [hrhs]
    have hmain : 2 * (t : ℝ) * ((t : ℝ) + 1) * lam ^ 2 ≤ 4 * (t : ℝ) ^ 2 * lam ^ 2 := by
      nlinarith [htprod, sq_nonneg lam]
    have hmain2 : 4 * (t : ℝ) ^ 2 * lam ^ 2 ≤ 4 * lam ^ 2 * Real.log (2 / δ) ^ 2 / lam' ^ 2 := by
      rw [le_div_iff₀ hlam'2]
      have h4 : 4 * lam ^ 2 * (t : ℝ) ^ 2 * lam' ^ 2 ≤ 4 * lam ^ 2 * Real.log (2 / δ) ^ 2 := by
        have hlam0' : (0 : ℝ) ≤ 4 * lam ^ 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hsq hlam0']
      nlinarith [h4]
    linarith [hmain, hmain2]
  calc Real.sqrt (fpsSuccessProbability lam δ t)
      ≤ Real.sqrt ((2 * (lam / lam') * Real.log (2 / δ)) ^ 2) := by
        apply Real.sqrt_le_sqrt
        calc fpsSuccessProbability lam δ t ≤ 2 * (t : ℝ) * ((t : ℝ) + 1) * lam ^ 2 := hmean
          _ ≤ (2 * (lam / lam') * Real.log (2 / δ)) ^ 2 := hkey
    _ = 2 * (lam / lam') * Real.log (2 / δ) := Real.sqrt_sq hR0

end Qatlib.Papers.GroundStPrep17.MainResults.LemmaOne
