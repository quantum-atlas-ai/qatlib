/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# The Grover amplitude block and its eigenvalue

The map `alphaGammaBlock` records a two-coordinate block in the small-error Grover analysis of
[Bulger2005]. This module proves its action on `(rotPhase θ, -1)` and computes the real part,
imaginary part, and squared norm of the resulting eigenvalue under explicit parameter relations.

## Main statements

* `alphaGammaBlock_chi_plus`: the eigenvector relation for the two-coordinate block.
* `chi_eigenvalue_re`: the eigenvalue's real part.
* `chi_eigenvalue_normSq`: the eigenvalue's squared norm.

## References

* [Bulger, 2005][Bulger2005]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QBasinHopping05.MainResults

/-- The complex unit-circle expression `cos θ + i sin θ`. -/
def rotPhase (θ : ℝ) : ℂ := (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I

/-- The complex two-coordinate map with diagonal entries `(a - b - c) / N` and `(a + b - c) / N`
and off-diagonal entries `-2u / N` and `2u / N`. -/
def alphaGammaBlock (a b c N u : ℝ) (v : ℂ × ℂ) : ℂ × ℂ :=
  ((((a - b - c) / N : ℝ) : ℂ) * v.1 - (((2 * u) / N : ℝ) : ℂ) * v.2,
   ((((2 * u) / N : ℝ) : ℂ) * v.1 + (((a + b - c) / N : ℝ) : ℂ) * v.2))

/-- If `N = a + b + c` is nonzero and `b = 2u cos θ`, the vector `(rotPhase θ, -1)` is an
eigenvector of `alphaGammaBlock` with the displayed eigenvalue [Bulger2005]. -/
theorem alphaGammaBlock_chi_plus (a b c N u θ : ℝ)
    (hN : N = a + b + c) (hN0 : N ≠ 0)
    (hb : b = 2 * u * Real.cos θ) :
    alphaGammaBlock a b c N u (rotPhase θ, -1)
      = ((((1 : ℝ) / N : ℝ) : ℂ)
          * (((a + b - c : ℝ) : ℂ) - ((2 * u : ℝ) : ℂ) * rotPhase θ) * rotPhase θ,
         (((1 : ℝ) / N : ℝ) : ℂ)
          * (((a + b - c : ℝ) : ℂ) - ((2 * u : ℝ) : ℂ) * rotPhase θ) * (-1)) := by
  subst hb
  subst hN
  refine Prod.ext ?_ ?_
  · apply Complex.ext
    · simp only [alphaGammaBlock, rotPhase, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero, sub_zero, mul_zero, neg_zero, zero_add]
      field_simp [hN0]
      linear_combination (-2 * u) * Real.sin_sq θ
    · simp only [alphaGammaBlock, rotPhase, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero, sub_zero, mul_zero, neg_zero, zero_add]
      field_simp [hN0]
      ring
  · apply Complex.ext
    · simp only [alphaGammaBlock, rotPhase, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero, sub_zero, mul_zero, neg_zero, zero_add]
      field_simp [hN0]
      ring
    · simp only [alphaGammaBlock, rotPhase, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero, sub_zero, mul_zero, neg_zero, zero_add]
      field_simp [hN0]
      ring

/-- Under `b = 2u cos θ`, the displayed block eigenvalue has real part `(a - c) / N`
[Bulger2005]. -/
theorem chi_eigenvalue_re (a b c N u θ : ℝ) (hb : b = 2 * u * Real.cos θ) :
    (Complex.re ((((1 : ℝ) / N : ℝ) : ℂ)
        * (((a + b - c : ℝ) : ℂ) - ((2 * u : ℝ) : ℂ) * rotPhase θ)))
      = (a - c) / N := by
  subst hb
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
    Complex.sub_im, rotPhase, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, zero_mul, sub_zero, add_zero, mul_one]
  ring

/-- The displayed block eigenvalue has imaginary part `-2u sin θ / N` [Bulger2005]. -/
theorem chi_eigenvalue_im (a b c N u θ : ℝ) :
    (Complex.im ((((1 : ℝ) / N : ℝ) : ℂ)
        * (((a + b - c : ℝ) : ℂ) - ((2 * u : ℝ) : ℂ) * rotPhase θ)))
      = -(2 * u * Real.sin θ) / N := by
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
    Complex.sub_im, rotPhase, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, zero_mul, sub_zero, add_zero, mul_one]
  ring

/-- Under `b = 2u cos θ`, `u ^ 2 = a * c`, and nonzero `N`, the displayed eigenvalue has squared
norm `((a + c) ^ 2 - b ^ 2) / N ^ 2` [Bulger2005]. -/
theorem chi_eigenvalue_normSq (a b c N u θ : ℝ)
    (hb : b = 2 * u * Real.cos θ) (hu : u ^ 2 = a * c) (hN0 : N ≠ 0) :
    Complex.normSq ((((1 : ℝ) / N : ℝ) : ℂ)
        * (((a + b - c : ℝ) : ℂ) - ((2 * u : ℝ) : ℂ) * rotPhase θ))
      = ((a + c) ^ 2 - b ^ 2) / N ^ 2 := by
  have hre := chi_eigenvalue_re a b c N u θ hb
  have him := chi_eigenvalue_im a b c N u θ
  have hb2 : b ^ 2 = 4 * u ^ 2 * Real.cos θ ^ 2 := by rw [hb]; ring
  have hsin := Real.sin_sq θ
  rw [Complex.normSq_apply, hre, him]
  field_simp
  nlinarith [hb2, hu, hsin]

end Qatlib.Papers.QBasinHopping05.MainResults
