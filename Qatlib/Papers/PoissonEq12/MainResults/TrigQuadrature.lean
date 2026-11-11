/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 1 and Lemma 2 of *Quantum algorithm and circuit design solving the Poisson
equation* (arXiv:1207.2485, Appendix 2)

The paper evaluates `sin x` on a grid by replacing `exp (i x)` with the `r`-th power of the
quadratic `W = 1 + i x / r - (x / r) ^ 2`, and proves

`|exp (i x) - W ^ r| ≤ 2 ^ 7 / r`   (Lemma 1)

for `x ∈ [π / (2 M), π / 2)` and `r = 2 ^ (ν + 7)`, together with the bounds on the real and
imaginary parts claimed in Lemma 2.

The paper's proof decomposes `exp (i y) = W + E (y)` and takes `E (y) = ∑_{k ≥ 3} (i y) ^ k / k!`.
With `W = 1 + i y - y ^ 2` (the value used in the proof of Proposition 1, where
`|W| ^ 2 = 1 - y ^ 2 + y ^ 4`) the remainder also carries `y ^ 2 / 2`, so this module bounds the
remainder directly as `|exp (i y) - W| ≤ y ^ 2 / 2 + y ^ 3 / 3` from the third-order Taylor bound
and then uses `|A ^ r - B ^ r| ≤ r |A - B|` for `|A|, |B| ≤ 1`.  The resulting error
`x ^ 2 / (2 r) + x ^ 3 / (3 r ^ 2)` is bounded by `2 ^ 7 / r` for `x ≤ π / 2`, which is the
paper's claim.
-/

namespace Qatlib.Papers.PoissonEq12.MainResults

set_option autoImplicit false

open Complex

/-- The quadratic `W = 1 + i y - y ^ 2` of Lemma 1, written in the normalised variable
`y = x / r`. -/
noncomputable def wQuad (y : ℝ) : ℂ := ((1 - y ^ 2 : ℝ) : ℂ) + (y : ℂ) * I

/-- The real part of `W = 1 + i y - y ^ 2`. -/
lemma wQuad_re (y : ℝ) : (wQuad y).re = 1 - y ^ 2 := by
  simp only [wQuad, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

/-- The imaginary part of `W = 1 + i y - y ^ 2`. -/
lemma wQuad_im (y : ℝ) : (wQuad y).im = y := by
  simp only [wQuad, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im]
  ring

/-- For `0 ≤ y ≤ 1` the quadratic `W = 1 + i y - y ^ 2` lies in the closed unit disk; this is
the paper's observation `|W| ^ 2 = 1 - y ^ 2 + y ^ 4 < 1`. -/
lemma norm_wQuad_le_one {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : ‖wQuad y‖ ≤ 1 := by
  have hsq : ‖wQuad y‖ ^ 2 = (1 - y ^ 2) ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, wQuad_re, wQuad_im]
    ring
  have h4 : y ^ 4 ≤ y ^ 2 := pow_le_pow_of_le_one hy0 hy1 (by norm_num)
  have h2 : ‖wQuad y‖ ^ 2 ≤ 1 := by
    rw [hsq]
    nlinarith
  nlinarith [norm_nonneg (wQuad y)]

/-- The second-order Taylor polynomial of `exp (i y)` is `1 + i y - y ^ 2 / 2`. -/
lemma taylor2_eq (y : ℝ) :
    1 + (y : ℂ) * I + ((y : ℂ) * I) ^ 2 / 2
      = ((1 - y ^ 2 / 2 : ℝ) : ℂ) + (y : ℂ) * I := by
  have hIsq : ((y : ℂ) * I) ^ 2 = -((y : ℂ) ^ 2) := by
    rw [mul_pow, pow_two I, Complex.I_mul_I]
    ring
  rw [hIsq]
  push_cast
  ring

/-- Third-order Taylor bound for `exp (i y)` in the exact form matching
`W = 1 + i y - y ^ 2`. -/
lemma norm_exp_mul_I_sub_quad_le {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 2) :
    ‖exp ((y : ℂ) * I) - (((1 - y ^ 2 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ y ^ 3 / 3 := by
  have hnorm : ‖(y : ℂ) * I‖ = y := by
    rw [Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hy0]
  have hb := Complex.exp_bound' (x := (y : ℂ) * I) (n := 3) (by rw [hnorm]; linarith)
  have hsum : (∑ m ∈ Finset.range 3, ((y : ℂ) * I) ^ m / ((m.factorial : ℕ) : ℂ))
      = 1 + (y : ℂ) * I + ((y : ℂ) * I) ^ 2 / 2 := by
    simp [Finset.sum_range_succ]
  rw [hsum, taylor2_eq, hnorm] at hb
  calc ‖exp ((y : ℂ) * I) - (((1 - y ^ 2 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖
      ≤ y ^ 3 / ((Nat.factorial 3 : ℕ) : ℝ) * 2 := hb
    _ = y ^ 3 / 3 := by
        rw [show ((Nat.factorial 3 : ℕ) : ℝ) = 6 by norm_num]
        ring

/-- The truncation error of `W = 1 + i y - y ^ 2` against `exp (i y)`: at most
`y ^ 2 / 2 + y ^ 3 / 3` for `0 ≤ y ≤ 2`. -/
lemma norm_exp_mul_I_sub_wQuad_le {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 2) :
    ‖exp ((y : ℂ) * I) - wQuad y‖ ≤ y ^ 2 / 2 + y ^ 3 / 3 := by
  have h := norm_exp_mul_I_sub_quad_le hy0 hy1
  have hd : (((1 - y ^ 2 / 2 : ℝ) : ℂ) + (y : ℂ) * I) - wQuad y
      = ((y ^ 2 / 2 : ℝ) : ℂ) := by
    rw [wQuad]
    push_cast
    ring
  have hsplit : exp ((y : ℂ) * I) - wQuad y
      = (exp ((y : ℂ) * I) - (((1 - y ^ 2 / 2 : ℝ) : ℂ) + (y : ℂ) * I))
        + ((y ^ 2 / 2 : ℝ) : ℂ) := by
    rw [← hd]
    abel
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have hreal : ‖((y ^ 2 / 2 : ℝ) : ℂ)‖ = y ^ 2 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hreal]
  linarith

/-- Powers of two complex numbers of modulus at most one are Lipschitz in the base with
constant `r`: `|A ^ r - B ^ r| ≤ r |A - B|`. -/
lemma norm_pow_sub_pow_le_mul {A B : ℂ} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (r : ℕ) :
    ‖A ^ r - B ^ r‖ ≤ (r : ℝ) * ‖A - B‖ := by
  induction r with
  | zero => simp
  | succ n ih =>
    have hdecomp : A ^ (n + 1) - B ^ (n + 1) = A ^ n * (A - B) + (A ^ n - B ^ n) * B := by
      ring
    have hAn : ‖A ^ n‖ ≤ 1 := by
      rw [Complex.norm_pow]
      exact pow_le_one₀ (norm_nonneg A) hA
    have h1 : ‖A ^ n * (A - B)‖ ≤ ‖A - B‖ := by
      rw [Complex.norm_mul]
      calc ‖A ^ n‖ * ‖A - B‖ ≤ 1 * ‖A - B‖ :=
            mul_le_mul_of_nonneg_right hAn (norm_nonneg (A - B))
        _ = ‖A - B‖ := one_mul _
    have h2 : ‖(A ^ n - B ^ n) * B‖ ≤ (n : ℝ) * ‖A - B‖ := by
      rw [Complex.norm_mul]
      calc ‖A ^ n - B ^ n‖ * ‖B‖ ≤ ((n : ℝ) * ‖A - B‖) * 1 := by
            refine mul_le_mul ih hB (norm_nonneg B) ?_
            exact mul_nonneg (by positivity) (norm_nonneg (A - B))
        _ = (n : ℝ) * ‖A - B‖ := by ring
    rw [hdecomp]
    calc ‖A ^ n * (A - B) + (A ^ n - B ^ n) * B‖
        ≤ ‖A ^ n * (A - B)‖ + ‖(A ^ n - B ^ n) * B‖ := norm_add_le _ _
      _ ≤ ‖A - B‖ + (n : ℝ) * ‖A - B‖ := add_le_add h1 h2
      _ = ((n : ℝ) + 1) * ‖A - B‖ := by ring
      _ = ((n + 1 : ℕ) : ℝ) * ‖A - B‖ := by push_cast; ring

/-- The elementary estimate behind Lemma 1: for `0 ≤ x ≤ 2` and `r = 2 ^ (ν + 7)`,
`x ^ 2 / (2 r) + x ^ 3 / (3 r ^ 2) ≤ 2 ^ 7 / r`. -/
lemma trig_error_le {ν : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 2) :
    x ^ 2 / (2 * (2 : ℝ) ^ (ν + 7)) + x ^ 3 / (3 * ((2 : ℝ) ^ (ν + 7)) ^ 2)
      ≤ 128 / (2 : ℝ) ^ (ν + 7) := by
  have hrpos : (0 : ℝ) < (2 : ℝ) ^ (ν + 7) := by positivity
  have hr1 : (1 : ℝ) ≤ (2 : ℝ) ^ (ν + 7) := one_le_pow₀ (by norm_num)
  have hmul : (x ^ 2 / (2 * (2 : ℝ) ^ (ν + 7))
        + x ^ 3 / (3 * ((2 : ℝ) ^ (ν + 7)) ^ 2)) * (2 : ℝ) ^ (ν + 7)
      = x ^ 2 / 2 + x ^ 3 / (3 * (2 : ℝ) ^ (ν + 7)) := by
    field_simp
  rw [le_div_iff₀ hrpos, hmul]
  have hx3 : x ^ 3 / (3 * (2 : ℝ) ^ (ν + 7)) ≤ 8 / 3 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hx0, hx2, hr1]
  have hx2' : x ^ 2 / 2 ≤ 2 := by
    nlinarith [hx0, hx2]
  linarith

/-- **Lemma 1** of arXiv:1207.2485: for `x ∈ [0, π / 2)` and `r = 2 ^ (ν + 7)` with `ν ≥ 1`,
`|exp (i x) - W ^ r| ≤ 2 ^ 7 / r` where `W = 1 + i x / r - (x / r) ^ 2`. -/
theorem lemma1 {ν : ℕ} (hν : 1 ≤ ν) {x : ℝ} (hx0 : 0 ≤ x) (hx : x < Real.pi / 2) :
    ‖exp ((x : ℂ) * I) - wQuad (x / (2 : ℝ) ^ (ν + 7)) ^ (2 ^ (ν + 7))‖ ≤
      128 / (2 : ℝ) ^ (ν + 7) := by
  have hcast : ((2 ^ (ν + 7) : ℕ) : ℝ) = (2 : ℝ) ^ (ν + 7) := by push_cast; ring
  have hrpos : (0 : ℝ) < (2 : ℝ) ^ (ν + 7) := by positivity
  have hr2 : (2 : ℝ) ≤ (2 : ℝ) ^ (ν + 7) := by
    have h1 : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ (ν + 7) := pow_le_pow_right₀ (by norm_num) (by omega)
    simpa using h1
  have hx2 : x ≤ 2 := by linarith [Real.pi_lt_four, Real.pi_pos]
  set y : ℝ := x / (2 : ℝ) ^ (ν + 7) with hy
  have hy0 : 0 ≤ y := by
    rw [hy]
    positivity
  have hy1 : y ≤ 1 := by
    rw [hy, div_le_iff₀ hrpos]
    linarith
  have hy2 : y ≤ 2 := by linarith
  have hW := norm_exp_mul_I_sub_wQuad_le hy0 hy2
  have hA : ‖exp ((y : ℂ) * I)‖ ≤ 1 := by
    simp
  have hexp : exp ((x : ℂ) * I) = exp ((y : ℂ) * I) ^ (2 ^ (ν + 7)) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    rw [hy]
    push_cast
    field_simp
  rw [hexp]
  refine (norm_pow_sub_pow_le_mul hA (norm_wQuad_le_one hy0 hy1) (2 ^ (ν + 7))).trans ?_
  rw [hcast]
  refine (mul_le_mul_of_nonneg_left hW (by positivity)).trans ?_
  have hmul_eq : ((2 : ℝ) ^ (ν + 7)) * (y ^ 2 / 2 + y ^ 3 / 3)
      = x ^ 2 / (2 * (2 : ℝ) ^ (ν + 7)) + x ^ 3 / (3 * ((2 : ℝ) ^ (ν + 7)) ^ 2) := by
    rw [hy]
    field_simp
  rw [hmul_eq]
  exact trig_error_le hx0 hx2

/-- The imaginary part of a complex number is bounded by its modulus. -/
lemma abs_im_le_norm' (z : ℂ) : |z.im| ≤ ‖z‖ := by
  have h : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have h2 : z.im ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [h]
    nlinarith [sq_nonneg z.re]
  nlinarith [abs_nonneg z.im, sq_abs z.im, norm_nonneg z]

/-- The real part of a complex number is bounded by its modulus. -/
lemma abs_re_le_norm' (z : ℂ) : |z.re| ≤ ‖z‖ := by
  have h : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have h2 : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [h]
    nlinarith [sq_nonneg z.im]
  nlinarith [abs_nonneg z.re, sq_abs z.re, norm_nonneg z]

/-- **Lemma 2** of arXiv:1207.2485, imaginary part: under the assumptions of Lemma 1,
`|sin x - Im (W ^ r)| ≤ 2 ^ 7 / r`. -/
theorem lemma2_sin {ν : ℕ} (hν : 1 ≤ ν) {x : ℝ} (hx0 : 0 ≤ x) (hx : x < Real.pi / 2) :
    |Real.sin x - (wQuad (x / (2 : ℝ) ^ (ν + 7)) ^ (2 ^ (ν + 7))).im| ≤
      128 / (2 : ℝ) ^ (ν + 7) := by
  have h := lemma1 hν hx0 hx
  have hsin : (exp ((x : ℂ) * I)).im = Real.sin x := Complex.exp_ofReal_mul_I_im x
  have him : |Real.sin x - (wQuad (x / (2 : ℝ) ^ (ν + 7)) ^ (2 ^ (ν + 7))).im|
      = |(exp ((x : ℂ) * I) - wQuad (x / (2 : ℝ) ^ (ν + 7)) ^ (2 ^ (ν + 7))).im| := by
    rw [Complex.sub_im, hsin]
  rw [him]
  exact (abs_im_le_norm' _).trans h

/-- **Lemma 2** of arXiv:1207.2485, real part: under the assumptions of Lemma 1,
`|cos x - Re (W ^ r)| ≤ 2 ^ 7 / r`. -/
theorem lemma2_cos {ν : ℕ} (hν : 1 ≤ ν) {x : ℝ} (hx0 : 0 ≤ x) (hx : x < Real.pi / 2) :
    |Real.cos x - (wQuad (x / (2 : ℝ) ^ (ν + 7)) ^ (2 ^ (ν + 7))).re| ≤
      128 / (2 : ℝ) ^ (ν + 7) := by
  have h := lemma1 hν hx0 hx
  have hcos : (exp ((x : ℂ) * I)).re = Real.cos x := Complex.exp_ofReal_mul_I_re x
  have hre : |Real.cos x - (wQuad (x / (2 : ℝ) ^ (ν + 7)) ^ (2 ^ (ν + 7))).re|
      = |(exp ((x : ℂ) * I) - wQuad (x / (2 : ℝ) ^ (ν + 7)) ^ (2 ^ (ν + 7))).re| := by
    rw [Complex.sub_re, hcos]
  rw [hre]
  exact (abs_re_le_norm' _).trans h

end Qatlib.Papers.PoissonEq12.MainResults
