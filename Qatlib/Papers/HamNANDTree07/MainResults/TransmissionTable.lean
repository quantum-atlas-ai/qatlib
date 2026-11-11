/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Low-energy transmission estimates for NAND trees

This module defines `sinTheta` and the complex transmission amplitude `transmissionCoeff`, then
controls their denominators by elementary norm estimates. Under |E| < 1/(16√N),
`section3_transmission_table` combines the reflection estimate for large |y| and the near-unit
transmission estimate for small |y|. See [FarhiGoldstoneGutmann2008] for the Hamiltonian
NAND-tree setting.

## Main statements

* `reflect_transmission_bound`: For N ≥ 1, nonzero E with |E| < 1 / (16√N), and |y| > 1 / (4√N
  |E|), the transmission amplitude has norm less than 8√N |E|.
* `transmit_transmission_bound`: For N ≥ 1, |E| < 1 / (16√N), and |y| < 4√N |E|, the
  transmission amplitude differs from 1 by norm less than 3√N |E|.
* `section3_transmission_table`: For N ≥ 1 and nonzero |E| < 1 / (16√N), combines the reflection
  bound for |y| > 1 / (4√N |E|) with the near-unit transmission bound for |y| < 4√N |E|.

## References

* [Farhi et al., 2008][FarhiGoldstoneGutmann2008]
-/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

namespace Qatlib.Papers.HamNANDTree07.MainResults.TransmissionTable

/-- The nonnegative quantity √(1 − E² / 4) used in the transmission formula. -/
def sinTheta (E : ℝ) : ℝ := Real.sqrt (1 - E ^ 2 / 4)

/-- The complex transmission amplitude 2i · `sinTheta E` / (2i · `sinTheta E` + y). -/
def transmissionCoeff (E y : ℝ) : ℂ :=
  (2 * sinTheta E * Complex.I) / (2 * sinTheta E * Complex.I + (y : ℂ))

/-- The quantity `sinTheta E` is nonnegative for every real E. -/
lemma sinTheta_nonneg (E : ℝ) : 0 ≤ sinTheta E := Real.sqrt_nonneg _

/-- The quantity `sinTheta E` is at most 1 for every real E. -/
lemma sinTheta_le_one (E : ℝ) : sinTheta E ≤ 1 := by
  rw [sinTheta, Real.sqrt_le_one]
  nlinarith [sq_nonneg E]

/-- If |E| < 2, then `sinTheta E` squared equals 1 − E² / 4. -/
lemma sinTheta_sq_of_abs_lt_two (E : ℝ) (hE : |E| < 2) :
    sinTheta E ^ 2 = 1 - E ^ 2 / 4 := by
  rw [sinTheta, Real.sq_sqrt]
  nlinarith [abs_nonneg E, sq_abs E, (abs_lt.mp hE).1, (abs_lt.mp hE).2]

/-- For N ≥ 1 and |E| < 1 / (16√N), `sinTheta E` is at least 3 / 4. -/
lemma sinTheta_ge_three_quarters (N : ℕ) (hN : 1 ≤ N) (E : ℝ)
    (hE : |E| < 1 / (16 * Real.sqrt N)) : 3 / 4 ≤ sinTheta E := by
  have hNpos : (0 : ℝ) < Real.sqrt N := by
    rw [Real.sqrt_pos]
    exact_mod_cast hN
  have hsqrt_ge_one : 1 ≤ Real.sqrt N := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hN)
  have hsmall : 1 / (16 * Real.sqrt N) ≤ 1 / 16 := by
    have h16 : (16 : ℝ) ≤ 16 * Real.sqrt N := by nlinarith
    exact one_div_le_one_div_of_le (by norm_num) h16
  have hE16 : |E| < 1 / 16 := lt_of_lt_of_le hE hsmall
  have hE2 : |E| < 2 := by linarith
  have hsq : sinTheta E ^ 2 = 1 - E ^ 2 / 4 := sinTheta_sq_of_abs_lt_two E hE2
  have hE2bound : E ^ 2 < 1 / 256 := by
    have h : |E| ^ 2 < (1 / 16 : ℝ) ^ 2 := by
      nlinarith [abs_nonneg E]
    nlinarith [h, sq_abs E]
  have hsq' : (3 / 4 : ℝ) ^ 2 ≤ sinTheta E ^ 2 := by
    rw [hsq]
    nlinarith
  exact le_of_sq_le_sq hsq' (sinTheta_nonneg E)

/-- The squared norm of the transmission denominator equals y² + 4 · `sinTheta E`². -/
lemma denom_norm_sq (E y : ℝ) :
    ‖2 * sinTheta E * Complex.I + (y : ℂ)‖ ^ 2 = y ^ 2 + 4 * sinTheta E ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- The absolute value of y is at most the norm of the transmission denominator. -/
lemma abs_le_denom_norm (E y : ℝ) :
    |y| ≤ ‖2 * sinTheta E * Complex.I + (y : ℂ)‖ := by
  have hsq := denom_norm_sq E y
  have hle : y ^ 2 ≤ ‖2 * sinTheta E * Complex.I + (y : ℂ)‖ ^ 2 := by
    rw [hsq]
    nlinarith [sq_nonneg (sinTheta E)]
  exact abs_le_of_sq_le_sq hle (norm_nonneg _)

/-- When `sinTheta E` is nonnegative, twice this quantity is at most the norm of the
transmission denominator. -/
lemma two_sin_le_denom_norm (E y : ℝ) (hs : 0 ≤ sinTheta E) :
    2 * sinTheta E ≤ ‖2 * sinTheta E * Complex.I + (y : ℂ)‖ := by
  have hsq := denom_norm_sq E y
  have hle : (2 * sinTheta E) ^ 2 ≤ ‖2 * sinTheta E * Complex.I + (y : ℂ)‖ ^ 2 := by
    rw [hsq]
    nlinarith [sq_nonneg y]
  have hnonneg : 0 ≤ 2 * sinTheta E := by positivity
  calc 2 * sinTheta E = |2 * sinTheta E| := (abs_of_nonneg hnonneg).symm
    _ ≤ ‖2 * sinTheta E * Complex.I + (y : ℂ)‖ :=
        abs_le_of_sq_le_sq hle (norm_nonneg _)

/-- When `sinTheta E` is nonnegative, the norm of 2i · `sinTheta E` equals 2 · `sinTheta E`. -/
lemma norm_two_sin_I (E : ℝ) (hs : 0 ≤ sinTheta E) :
    ‖2 * sinTheta E * Complex.I‖ = 2 * sinTheta E := by
  rw [norm_mul, norm_mul, Complex.norm_I, mul_one]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
  norm_num

/-- For N ≥ 1, nonzero E with |E| < 1 / (16√N), and |y| > 1 / (4√N |E|), the transmission
amplitude has norm less than 8√N |E|. See [FarhiGoldstoneGutmann2008]. -/
theorem reflect_transmission_bound (N : ℕ) (hN : 1 ≤ N) (E y : ℝ)
    (hE0 : E ≠ 0)
    (hE : |E| < 1 / (16 * Real.sqrt N))
    (hy : 1 / (4 * Real.sqrt N * |E|) < |y|) :
    ‖transmissionCoeff E y‖ < 8 * Real.sqrt N * |E| := by
  have hNpos : (0 : ℝ) < Real.sqrt N := by
    rw [Real.sqrt_pos]
    exact_mod_cast hN
  have hs0 : 0 ≤ sinTheta E := sinTheta_nonneg E
  have hs1 : sinTheta E ≤ 1 := sinTheta_le_one E
  have hEpos : 0 < |E| := abs_pos.mpr hE0
  have hypos : 0 < |y| := lt_of_le_of_lt (by positivity) hy
  have hdenpos : 0 < ‖2 * sinTheta E * Complex.I + (y : ℂ)‖ :=
    lt_of_lt_of_le hypos (abs_le_denom_norm E y)
  rw [transmissionCoeff, norm_div, norm_two_sin_I E hs0]
  have hstep1 : 2 * sinTheta E / ‖2 * sinTheta E * Complex.I + (y : ℂ)‖ ≤
      2 * sinTheta E / |y| :=
    div_le_div_of_nonneg_left (by linarith) hypos (abs_le_denom_norm E y)
  have hstep2 : 2 * sinTheta E / |y| ≤ 2 / |y| :=
    div_le_div_of_nonneg_right (by linarith) (abs_nonneg y)
  have hstep3 : 2 / |y| < 8 * Real.sqrt N * |E| := by
    rw [div_lt_iff₀ hypos]
    have hkey : 1 < 4 * Real.sqrt N * |E| * |y| := by
      have := (div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * Real.sqrt N * |E|)).mp hy
      nlinarith
    nlinarith
  exact lt_of_le_of_lt (le_trans hstep1 hstep2) hstep3

/-- For N ≥ 1, |E| < 1 / (16√N), and |y| < 4√N |E|, the transmission amplitude differs from 1 by
norm less than 3√N |E|. See [FarhiGoldstoneGutmann2008]. -/
theorem transmit_transmission_bound (N : ℕ) (hN : 1 ≤ N) (E y : ℝ)
    (hE : |E| < 1 / (16 * Real.sqrt N))
    (hy : |y| < 4 * Real.sqrt N * |E|) :
    ‖transmissionCoeff E y - 1‖ < 3 * Real.sqrt N * |E| := by
  have hNpos : (0 : ℝ) < Real.sqrt N := by
    rw [Real.sqrt_pos]
    exact_mod_cast hN
  have hs : 3 / 4 ≤ sinTheta E := sinTheta_ge_three_quarters N hN E hE
  have hs0 : 0 ≤ sinTheta E := sinTheta_nonneg E

  have hEpos : 0 < |E| := by
    have h : 0 < 4 * Real.sqrt N * |E| := lt_of_le_of_lt (abs_nonneg y) hy
    have h4 : (0 : ℝ) < 4 * Real.sqrt N := by positivity
    nlinarith [h, h4, abs_nonneg E]
  have hs_pos : 0 < sinTheta E := lt_of_lt_of_le (by norm_num) hs
  have hdenpos : 0 < ‖2 * sinTheta E * Complex.I + (y : ℂ)‖ :=
    lt_of_lt_of_le (by linarith : (0 : ℝ) < 2 * sinTheta E)
      (two_sin_le_denom_norm E y hs0)
  have hzne : 2 * sinTheta E * Complex.I + (y : ℂ) ≠ 0 := by
    intro hzero
    have him : (2 * sinTheta E * Complex.I + (y : ℂ)).im = 0 := by rw [hzero]; simp
    simp at him
    linarith

  have hsub : transmissionCoeff E y - 1 =
      (-(y : ℂ)) / (2 * sinTheta E * Complex.I + (y : ℂ)) := by
    rw [transmissionCoeff, div_sub_one hzne]
    have hnum : 2 * sinTheta E * Complex.I -
        (2 * sinTheta E * Complex.I + (y : ℂ)) = -(y : ℂ) := by ring
    rw [hnum]
  have hnorm : ‖transmissionCoeff E y - 1‖ =
      |y| / ‖2 * sinTheta E * Complex.I + (y : ℂ)‖ := by
    rw [hsub, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs]
  have hstep1 : |y| / ‖2 * sinTheta E * Complex.I + (y : ℂ)‖ ≤ |y| / (2 * sinTheta E) :=
    div_le_div_of_nonneg_left (abs_nonneg y) (by linarith)
      (two_sin_le_denom_norm E y hs0)
  have hstep2 : |y| / (2 * sinTheta E) ≤ |y| / (3 / 2) :=
    div_le_div_of_nonneg_left (abs_nonneg y) (by norm_num) (by linarith)
  have hstep3 : |y| / (3 / 2) = (2 / 3) * |y| := by ring
  have hstep4 : (2 / 3) * |y| < 3 * Real.sqrt N * |E| := by
    have hscale : (2 / 3) * |y| < (2 / 3) * (4 * Real.sqrt N * |E|) := by
      exact mul_lt_mul_of_pos_left hy (by norm_num)
    have hprod : 0 < Real.sqrt N * |E| := mul_pos hNpos hEpos
    nlinarith
  calc ‖transmissionCoeff E y - 1‖
      = |y| / ‖2 * sinTheta E * Complex.I + (y : ℂ)‖ := hnorm
    _ ≤ |y| / (2 * sinTheta E) := hstep1
    _ ≤ |y| / (3 / 2) := hstep2
    _ = (2 / 3) * |y| := hstep3
    _ < 3 * Real.sqrt N * |E| := hstep4

/-- For N ≥ 1 and nonzero |E| < 1 / (16√N), combines the reflection bound for |y| > 1 / (4√N
|E|) with the near-unit transmission bound for |y| < 4√N |E|. See
[FarhiGoldstoneGutmann2008]. -/
theorem section3_transmission_table (N : ℕ) (hN : 1 ≤ N) (E y : ℝ)
    (hE0 : E ≠ 0) (hE : |E| < 1 / (16 * Real.sqrt N)) :
    (1 / (4 * Real.sqrt N * |E|) < |y| →
        ‖transmissionCoeff E y‖ < 8 * Real.sqrt N * |E|) ∧
    (|y| < 4 * Real.sqrt N * |E| →
        ‖transmissionCoeff E y - 1‖ < 3 * Real.sqrt N * |E|) :=
  ⟨reflect_transmission_bound N hN E y hE0 hE, transmit_transmission_bound N hN E y hE⟩

end Qatlib.Papers.HamNANDTree07.MainResults.TransmissionTable
