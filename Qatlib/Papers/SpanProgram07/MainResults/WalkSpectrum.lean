/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SpanProgram07.MainResults

open Complex

def walkEigen (lam : ℝ) (s : Bool) : ℂ :=
  ((if s then Real.sqrt (1 - lam ^ 2) else -Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ)
    + (lam : ℂ) * Complex.I

theorem walkEigen_modulus {lam : ℝ} (h : lam ^ 2 ≤ 1) (s : Bool) :
    ‖walkEigen lam s‖ = 1 := by
  have h1 : 0 ≤ 1 - lam ^ 2 := by linarith
  have hs : (Real.sqrt (1 - lam ^ 2)) ^ 2 = 1 - lam ^ 2 := Real.sq_sqrt h1
  have hxe : (if s then Real.sqrt (1 - lam ^ 2) else -Real.sqrt (1 - lam ^ 2)) ^ 2
      = 1 - lam ^ 2 := by
    cases s with
    | true => simpa using hs
    | false => simpa using hs
  have hsq : Complex.normSq (walkEigen lam s) = 1 := by
    rw [walkEigen, Complex.normSq_add_mul_I, hxe]
    ring
  have heq := Complex.normSq_eq_norm_sq (walkEigen lam s)
  rw [hsq] at heq
  nlinarith [norm_nonneg (walkEigen lam s)]

theorem root_general (x y : ℝ) (hx : x ^ 2 + y ^ 2 = 1) :
    (((x : ℝ) : ℂ) + (y : ℂ) * Complex.I) ^ 2
      - 2 * Complex.I * (y : ℂ) * (((x : ℝ) : ℂ) + (y : ℂ) * Complex.I) - 1 = 0 := by
  have hI : Complex.I * Complex.I + 1 = 0 := by
    rw [Complex.I_mul_I]; ring
  have hx' : ((x : ℝ) : ℂ) ^ 2 + ((y : ℝ) : ℂ) ^ 2 - 1 = 0 := by
    have hsum : ((x : ℝ) : ℂ) ^ 2 + ((y : ℝ) : ℂ) ^ 2 = 1 := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add, hx]
      norm_num
    exact sub_eq_zero.mpr hsum
  linear_combination hx' + (-((y : ℝ) : ℂ) ^ 2) * hI

theorem walkEigen_root {lam : ℝ} (h : lam ^ 2 ≤ 1) (s : Bool) :
    (walkEigen lam s) ^ 2 - 2 * Complex.I * (lam : ℂ) * walkEigen lam s - 1 = 0 := by
  have h1 : 0 ≤ 1 - lam ^ 2 := by linarith
  have hs : (Real.sqrt (1 - lam ^ 2)) ^ 2 = 1 - lam ^ 2 := Real.sq_sqrt h1
  have hx : (if s then Real.sqrt (1 - lam ^ 2) else -Real.sqrt (1 - lam ^ 2)) ^ 2
      + lam ^ 2 = 1 := by
    have hxe : (if s then Real.sqrt (1 - lam ^ 2) else -Real.sqrt (1 - lam ^ 2)) ^ 2
        = 1 - lam ^ 2 := by
      cases s with
      | true => simpa using hs
      | false => simpa using hs
    rw [hxe]; ring
  rw [walkEigen]
  exact root_general _ _ hx

theorem walkEigen_true_eq_one {lam : ℝ} (h : lam ^ 2 ≤ 1) :
    walkEigen lam true = 1 ↔ lam = 0 := by
  constructor
  · intro he
    have him := congr_arg Complex.im he
    simpa [walkEigen] using him
  · intro hl
    subst hl
    simp [walkEigen]

theorem walkEigen_false_eq_neg_one {lam : ℝ} (h : lam ^ 2 ≤ 1) :
    walkEigen lam false = -1 ↔ lam = 0 := by
  constructor
  · intro he
    have him := congr_arg Complex.im he
    simpa [walkEigen] using him
  · intro hl
    subst hl
    norm_num [walkEigen]

theorem amp_soundness {lam w Adv aO bO c3 : ℝ} (hlam : 0 < lam) (hw : 0 < w)
    (hbO : bO ≠ 0) (hrel : lam * aO = w * bO)
    (hbound : |aO| ≤ c3 * (lam * Adv / w) * |bO|) :
    w ^ 2 ≤ c3 * lam ^ 2 * Adv := by
  have habs : |aO| = w * |bO| / lam := by
    have haO : aO = w * bO / lam := by field_simp; linarith
    rw [haO, abs_div, abs_mul, abs_of_pos hw, abs_of_pos hlam]
  have h2 : w * |bO| / lam ≤ c3 * (lam * Adv / w) * |bO| := by
    rw [← habs]; exact hbound
  have hbOpos : 0 < |bO| := abs_pos.mpr hbO
  have hA : (w / lam) * |bO| ≤ (c3 * (lam * Adv / w)) * |bO| := by
    calc (w / lam) * |bO| = w * |bO| / lam := by ring
      _ ≤ c3 * (lam * Adv / w) * |bO| := h2
  have h3 : w / lam ≤ c3 * (lam * Adv / w) := le_of_mul_le_mul_right hA hbOpos
  have h4 : (w / lam) * w ≤ (c3 * (lam * Adv / w)) * w :=
    mul_le_mul_of_nonneg_right h3 (le_of_lt hw)
  have h4' : w ^ 2 / lam ≤ c3 * lam * Adv := by
    calc w ^ 2 / lam = (w / lam) * w := by field_simp
      _ ≤ (c3 * (lam * Adv / w)) * w := h4
      _ = c3 * lam * Adv := by field_simp
  rw [div_le_iff₀ hlam] at h4'
  nlinarith [h4']

end Qatlib.Papers.SpanProgram07.MainResults
