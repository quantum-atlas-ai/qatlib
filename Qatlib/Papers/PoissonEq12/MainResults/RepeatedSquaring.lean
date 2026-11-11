/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PoissonEq12.MainResults.TrigQuadrature
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 1 of *Quantum algorithm and circuit design solving the Poisson equation*
(arXiv:1207.2485, Appendix 2)

The paper computes `W ^ r`, `r = 2 ^ (ν + 7)`, by repeated squaring in fixed-precision
arithmetic and claims the accumulated error bound `|W ^ r - Ŵ_r| ≤ 2 ^ (ν + 9) / 2 ^ s`
for `s`-bit arithmetic (`s ≥ 11 + ν + log₂ M`).

The formalisation models the arithmetic by a `BitTruncation s`: a rounding map whose values are
within `√2 · 2⁻ˢ` of their argument (truncating the real and imaginary parts separately gives
exactly this) and which never increases the modulus.  The accumulation is the paper's argument
with the Jacobian bound `‖J‖ ≤ 2` replaced by the elementary estimate
`|z² - w²| = |z + w| |z - w| ≤ 2 |z - w|` for `|z|, |w| ≤ 1`.  This gives
`((2 ^ (ν + 8)) - 1) · √2 / 2 ^ s ≤ 2 ^ (ν + 9) / 2 ^ s`, the paper's bound.

The paper's side condition `s ≥ 11 + ν + log₂ M` enters only through the requirement that the
rounded initial value stays in the unit disk; here that is the `trunc_contract` field, so the
bound is stated for every `s`.
-/

namespace Qatlib.Papers.PoissonEq12.MainResults

set_option autoImplicit false

open Complex

/-- A fixed-precision arithmetic of `s` fractional bits: every complex number is replaced by
one within `√2 · 2⁻ˢ` of it (the two real coordinates truncated separately), and truncation
never increases the modulus. -/
structure BitTruncation (s : ℕ) where
  /-- The rounding map of the fixed-precision arithmetic. -/
  trunc : ℂ → ℂ
  /-- Each coordinate is truncated to `s` bits, so the modulus error is at most `√2 · 2⁻ˢ`. -/
  trunc_close : ∀ z, ‖trunc z - z‖ ≤ Real.sqrt 2 / 2 ^ s
  /-- Truncating the real and imaginary parts separately never increases the modulus. -/
  trunc_contract : ∀ z, ‖trunc z‖ ≤ ‖z‖

/-- The repeated-squaring evaluation of `W ^ r` under the fixed-precision arithmetic `T`:
the initial value is truncated, and every squaring is truncated. -/
noncomputable def repeatedSquaring {s : ℕ} (T : BitTruncation s) (w : ℂ) (j : ℕ) : ℂ :=
  Nat.rec (T.trunc w) (fun _ z => T.trunc (z ^ 2)) j

/-- The initial step of the repeated squaring. -/
@[simp] lemma repeatedSquaring_zero {s : ℕ} (T : BitTruncation s) (w : ℂ) :
    repeatedSquaring T w 0 = T.trunc w := rfl

/-- Each squaring step of the repeated squaring. -/
@[simp] lemma repeatedSquaring_succ {s : ℕ} (T : BitTruncation s) (w : ℂ) (j : ℕ) :
    repeatedSquaring T w (j + 1) = T.trunc ((repeatedSquaring T w j) ^ 2) := rfl

/-- Every value produced by the repeated squaring of a number of modulus at most one stays in
the closed unit disk; this is the paper's observation that all `Ŵ_{2^j}` lie in the unit disk. -/
lemma norm_repeatedSquaring_le_one {s : ℕ} (T : BitTruncation s) {W : ℂ} (hW : ‖W‖ ≤ 1)
    (j : ℕ) : ‖repeatedSquaring T W j‖ ≤ 1 := by
  induction j with
  | zero => exact (T.trunc_contract W).trans hW
  | succ n ih =>
    rw [repeatedSquaring_succ]
    refine (T.trunc_contract _).trans ?_
    rw [Complex.norm_pow]
    nlinarith [ih, norm_nonneg (repeatedSquaring T W n)]

/-- The error accumulation of the paper's Proposition 1: after `j` squarings the error is at
most `(2 ^ (j + 1) - 1) · √2 / 2 ^ s`. -/
lemma repeatedSquaring_error {s : ℕ} (T : BitTruncation s) {W : ℂ} (hW : ‖W‖ ≤ 1) (j : ℕ) :
    ‖W ^ 2 ^ j - repeatedSquaring T W j‖
      ≤ ((2 : ℝ) ^ (j + 1) - 1) * (Real.sqrt 2 / 2 ^ s) := by
  have hδ : (0 : ℝ) ≤ Real.sqrt 2 / 2 ^ s := by positivity
  induction j with
  | zero =>
      have h := T.trunc_close W
      rw [norm_sub_rev] at h
      have h1 : ((2 : ℝ) ^ (0 + 1) - 1) * (Real.sqrt 2 / 2 ^ s) = Real.sqrt 2 / 2 ^ s := by
        norm_num
      rw [h1]
      simpa using h
  | succ n ih =>
    have hsq : W ^ 2 ^ (n + 1) = (W ^ 2 ^ n) ^ 2 := by
      rw [pow_succ, pow_mul]
    have hA : ‖W ^ 2 ^ n‖ ≤ 1 := by
      rw [Complex.norm_pow]
      exact pow_le_one₀ (norm_nonneg W) hW
    have hB : ‖repeatedSquaring T W n‖ ≤ 1 := norm_repeatedSquaring_le_one T hW n
    have h1 : ‖(W ^ 2 ^ n) ^ 2 - (repeatedSquaring T W n) ^ 2‖
        ≤ 2 * ‖W ^ 2 ^ n - repeatedSquaring T W n‖ := by
      have hfac : (W ^ 2 ^ n) ^ 2 - (repeatedSquaring T W n) ^ 2
          = (W ^ 2 ^ n + repeatedSquaring T W n) * (W ^ 2 ^ n - repeatedSquaring T W n) := by
        ring
      rw [hfac, Complex.norm_mul]
      have hsum : ‖W ^ 2 ^ n + repeatedSquaring T W n‖ ≤ 2 := by
        refine (norm_add_le _ _).trans ?_
        linarith
      nlinarith [hsum, norm_nonneg (W ^ 2 ^ n - repeatedSquaring T W n)]
    have hstep : ‖W ^ 2 ^ (n + 1) - repeatedSquaring T W (n + 1)‖
        ≤ 2 * ‖W ^ 2 ^ n - repeatedSquaring T W n‖ + Real.sqrt 2 / 2 ^ s := by
      rw [hsq, repeatedSquaring_succ]
      have hdecomp : (W ^ 2 ^ n) ^ 2 - T.trunc ((repeatedSquaring T W n) ^ 2)
          = ((W ^ 2 ^ n) ^ 2 - (repeatedSquaring T W n) ^ 2)
            + ((repeatedSquaring T W n) ^ 2 - T.trunc ((repeatedSquaring T W n) ^ 2)) := by
        ring
      rw [hdecomp]
      have hc := T.trunc_close ((repeatedSquaring T W n) ^ 2)
      rw [norm_sub_rev] at hc
      exact (norm_add_le _ _).trans (add_le_add h1 hc)
    have hpow : (2 : ℝ) ^ (n + 2) = 2 * 2 ^ (n + 1) := by
      rw [show n + 2 = n + 1 + 1 by omega, pow_succ]
      ring
    calc ‖W ^ 2 ^ (n + 1) - repeatedSquaring T W (n + 1)‖
        ≤ 2 * ‖W ^ 2 ^ n - repeatedSquaring T W n‖ + Real.sqrt 2 / 2 ^ s := hstep
      _ ≤ 2 * (((2 : ℝ) ^ (n + 1) - 1) * (Real.sqrt 2 / 2 ^ s)) + Real.sqrt 2 / 2 ^ s := by
          have hm := mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 2)
          linarith
      _ = ((2 : ℝ) ^ (n + 2) - 1) * (Real.sqrt 2 / 2 ^ s) := by
          rw [hpow]
          ring

/-- **Proposition 1** of arXiv:1207.2485: repeated squaring of `W = 1 + i y - y ^ 2` in
`s`-bit fixed-precision arithmetic accumulates an error of at most `2 ^ (ν + 9) / 2 ^ s` over
`ν + 7` squarings, i.e. `|W ^ r - Ŵ_r| ≤ 2 ^ (ν + 9) / 2 ^ s` for `r = 2 ^ (ν + 7)`.

The paper assumes `ν ≥ 1`, which makes `r = 2 ^ (ν + 7) ≥ 256` and lets the side condition
`s ≥ 11 + ν + log₂ M` keep the truncated initial value in the unit disk.  Here that last fact is
the `trunc_contract` field of the arithmetic, so the bound holds for every `ν`. -/
theorem prop1 {ν : ℕ} {s : ℕ} (T : BitTruncation s) {y : ℝ} (hy0 : 0 ≤ y)
    (hy1 : y ≤ 1) :
    ‖wQuad y ^ 2 ^ (ν + 7) - repeatedSquaring T (wQuad y) (ν + 7)‖
      ≤ (2 : ℝ) ^ (ν + 9) / 2 ^ s := by
  have hW : ‖wQuad y‖ ≤ 1 := norm_wQuad_le_one hy0 hy1
  have herr := repeatedSquaring_error T hW (ν + 7)
  rw [show ν + 7 + 1 = ν + 8 by omega] at herr
  refine herr.trans ?_
  have hsqrt : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hδ : Real.sqrt 2 / 2 ^ s ≤ 2 / 2 ^ s := by gcongr
  calc ((2 : ℝ) ^ (ν + 8) - 1) * (Real.sqrt 2 / 2 ^ s)
      ≤ (2 : ℝ) ^ (ν + 8) * (2 / 2 ^ s) := by
        refine mul_le_mul (by linarith) hδ (by positivity) (by positivity)
    _ = (2 : ℝ) ^ (ν + 9) / 2 ^ s := by
        rw [show ν + 9 = ν + 8 + 1 by omega, pow_succ]
        ring

end Qatlib.Papers.PoissonEq12.MainResults
