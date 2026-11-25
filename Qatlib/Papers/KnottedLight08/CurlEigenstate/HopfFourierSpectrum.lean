/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Fin.VecNotation

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Radial factor of the published Hopf Fourier coefficients

The Fourier coefficients in Supplementary Methods 1, equations
(6) and (7), are homogeneous quadratic numerators multiplied by
`π exp(-k)/k`. On each ray their common radial amplitude is the
`k exp(-k)` factor displayed in equation (5) of the article.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.CurlEigenstate

open scoped BigOperators

/-- The quadratic numerator of the published magnetic Fourier coefficient. -/
def hopfMagneticFourierPoly (k x y z : ℝ) : Fin 3 → ℂ :=
  ![(y : ℂ) ^ 2 + (z : ℂ) ^ 2,
    Complex.I * (k : ℂ) * (z : ℂ) - (x : ℂ) * (y : ℂ),
    -(Complex.I * (k : ℂ) * (y : ℂ)) - (x : ℂ) * (z : ℂ)]

/-- The quadratic numerator of the published electric Fourier coefficient. -/
def hopfElectricFourierPoly (k x y z : ℝ) : Fin 3 → ℂ :=
  ![-(Complex.I * (k : ℂ) * (z : ℂ)) - (x : ℂ) * (y : ℂ),
    (x : ℂ) ^ 2 + (z : ℂ) ^ 2,
    Complex.I * (k : ℂ) * (x : ℂ) - (y : ℂ) * (z : ℂ)]

/-- The Fourier coefficient in Supplementary Methods 1, equation (6). -/
noncomputable def hopfMagneticFourier (k x y z : ℝ) (j : Fin 3) : ℂ :=
  (Real.pi : ℂ) * (Real.exp (-k) : ℂ) / (k : ℂ) * hopfMagneticFourierPoly k x y z j

/-- The Fourier coefficient in Supplementary Methods 1, equation (7). -/
noncomputable def hopfElectricFourier (k x y z : ℝ) (j : Fin 3) : ℂ :=
  (Real.pi : ℂ) * (Real.exp (-k) : ℂ) / (k : ℂ) * hopfElectricFourierPoly k x y z j

/-- The common radial amplitude of the two published Fourier coefficients. -/
noncomputable def hopfFrequencyFactor (k : ℝ) : ℝ :=
  k * Real.exp (-k)

/-- The radial factor in the article is strictly positive at every positive frequency. -/
theorem hopfFrequencyFactor_pos {k : ℝ} (hk : 0 < k) : 0 < hopfFrequencyFactor k :=
  mul_pos hk (Real.exp_pos _)

/-- Along a ray both published Fourier coefficients separate into the same
radial factor and a frequency-independent angular polynomial. -/
theorem hopfFourier_eq_frequencyFactor {k : ℝ} (hk : k ≠ 0) (x y z : ℝ) (j : Fin 3) :
    hopfMagneticFourier k (k * x) (k * y) (k * z) j =
      (Real.pi : ℂ) * (hopfFrequencyFactor k : ℂ) * hopfMagneticFourierPoly 1 x y z j ∧
    hopfElectricFourier k (k * x) (k * y) (k * z) j =
      (Real.pi : ℂ) * (hopfFrequencyFactor k : ℂ) * hopfElectricFourierPoly 1 x y z j := by
  have hkC : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  constructor
  · fin_cases j <;> simp only [hopfMagneticFourier, hopfMagneticFourierPoly, hopfFrequencyFactor] <;>
      push_cast <;> field_simp [hkC]
  · fin_cases j <;> simp only [hopfElectricFourier, hopfElectricFourierPoly, hopfFrequencyFactor] <;>
      push_cast <;> field_simp [hkC]

/-- The polarization-summed squared angular amplitude is positive at every
unit direction. Radial amplitude and quadratic energy density are distinct. -/
theorem hopfFourier_angular_sq (x y z : ℝ) (h : x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    (∑ j : Fin 3, (‖hopfMagneticFourierPoly 1 x y z j‖ ^ 2 +
      ‖hopfElectricFourierPoly 1 x y z j‖ ^ 2)) = 2 * (1 + z ^ 2) := by
  simp only [Fin.sum_univ_three, hopfMagneticFourierPoly, hopfElectricFourierPoly,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
    Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.ofReal_one, mul_one,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    pow_two, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  linear_combination (x ^ 2 + y ^ 2 + 2 * z ^ 2 + 2) * h

end Qatlib.Papers.KnottedLight08.CurlEigenstate
