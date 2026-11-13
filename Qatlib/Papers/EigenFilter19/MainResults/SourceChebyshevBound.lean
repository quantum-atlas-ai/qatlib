/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Arcosh

set_option backward.isDefEq.respectTransparency false

/-!
# Exponential Lower Bound for Chebyshev Polynomials Above One

This module proves Lemma 13: for `0 ≤ δ ≤ 3 - 2√2` and every degree `ℓ : ℕ`,
the Chebyshev polynomial of the first kind satisfies
`T_ℓ(1 + δ) ≥ (1 / 2) exp(ℓ √δ)`.

## Main statements

* `source_lemma13_chebyshev_lower`: `(1 / 2) * exp (ℓ * √δ) ≤ (Chebyshev.T ℝ ℓ).eval (1 + δ)`.

## References

* [Lin and Tong, 2020][LinTong2020EigenFilter], Lemma 13, Appendix E, p. 32.
-/

set_option autoImplicit false
noncomputable section

open Polynomial
open scoped Classical BigOperators

namespace Qatlib.Papers.EigenFilter19.MainResults

/-- **Lemma 13**: for `0 ≤ δ ≤ 3 - 2√2`, the `ℓ`-th Chebyshev polynomial at `1 + δ`
dominates `(1 / 2) e^{ℓ √δ}`. -/
theorem source_lemma13_chebyshev_lower (ℓ : ℕ) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 - 2 * Real.sqrt 2) :
    (1 / 2 : ℝ) * Real.exp ((ℓ : ℝ) * Real.sqrt δ) ≤
      (Polynomial.Chebyshev.T ℝ (ℓ : ℤ)).eval (1 + δ) := by
  let t := Real.sqrt δ
  have ht0 : 0 ≤ t := Real.sqrt_nonneg δ
  have ht2 : t ^ 2 = δ := Real.sq_sqrt hδ0
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs1 : 1 ≤ Real.sqrt 2 := by nlinarith
  have hts : t ≤ Real.sqrt 2 - 1 := by nlinarith
  have ht : t ≤ 1 / 2 := by nlinarith
  let b := Real.exp (-t)
  have hb0 : 0 < b := Real.exp_pos (-t)
  have hb1 : b ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hbt : 1 - t ≤ b := by
    have := Real.add_one_le_exp (-t)
    linarith
  have heb : Real.exp t * b = 1 := by
    dsimp [b]
    rw [Real.exp_neg, mul_inv_cancel₀ (Real.exp_ne_zero t)]
  have hb2 : (1 - b) ^ 2 ≤ t ^ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ t - (1 - b))
      (by linarith : 0 ≤ t + (1 - b))]
  have he : Real.exp t + b ≤ 2 + 2 * t ^ 2 := by
    apply (mul_le_mul_iff_right₀ hb0).mp
    nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * b - 1) (sq_nonneg t)]
  have hc : Real.cosh t ≤ 1 + δ := by
    rw [Real.cosh_eq]
    change (Real.exp t + b) / 2 ≤ 1 + δ
    nlinarith
  have hδ : 1 ≤ 1 + δ := by linarith
  have htθ : t ≤ Real.arcosh (1 + δ) := by
    rw [← Real.arcosh_cosh ht0]
    exact (Real.arcosh_le_arcosh (Real.cosh_pos t) (by linarith)).mpr hc
  rw [← Real.cosh_arcosh hδ, Polynomial.Chebyshev.T_real_cosh]
  simp only [Int.cast_natCast]
  calc
    (1 / 2 : ℝ) * Real.exp ((ℓ : ℝ) * t) ≤
        (1 / 2 : ℝ) * Real.exp ((ℓ : ℝ) * Real.arcosh (1 + δ)) := by
      gcongr
    _ ≤ Real.cosh ((ℓ : ℝ) * Real.arcosh (1 + δ)) := by
      rw [Real.cosh_eq]
      linarith [Real.exp_pos (-((ℓ : ℝ) * Real.arcosh (1 + δ)))]

end Qatlib.Papers.EigenFilter19.MainResults
