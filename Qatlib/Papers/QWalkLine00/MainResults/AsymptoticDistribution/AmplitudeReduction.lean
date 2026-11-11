/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkLine00.MainResults.WalkModel.HadamardEigen
import Qatlib.Papers.QWalkLine00.MainResults.WalkModel.StationaryAndFamily
import Qatlib.Papers.QWalkLine00.MainResults.AsymptoticDistribution.Basic
import Mathlib.Analysis.Complex.Norm

/-!
# Algebra of leading Hadamard amplitudes

The functions `leadAmpL` and `leadAmpR` express the oscillatory coefficients in the proposed
asymptotic probability formula of [NayakVishwanath2000]. This module rewrites `asymProb` as a
nonnegative prefactor times a sum of squares in the interior regime, and verifies unitarity of
the Fourier kernel and unit modulus of its eigenvalues.

## Main statements

* `asymBracket_eq_sq_sum`: rewrites the oscillatory bracket as two squared amplitudes.
* `asymProb_nonneg`: proves nonnegativity in the interior regime.
* `hadamardKernel_unitary`: verifies the Fourier kernel identity `U† * U = 1`.

## References

* [Nayak and Vishwanath, 2000][NayakVishwanath2000]
-/

set_option warningAsError false

namespace Qatlib.Papers.QWalkLine00.MainResults

set_option autoImplicit false

open Real

noncomputable section

/-- The parity weight is nonnegative. -/
theorem parityWeight_nonneg (n : ℤ) (t : ℕ) : 0 ≤ parityWeight n t := by
  unfold parityWeight
  split_ifs <;> norm_num

/-- The square of the parity weight equals twice the parity weight. See [NayakVishwanath2000]. -/
theorem parityWeight_sq (n : ℤ) (t : ℕ) :
    parityWeight n t ^ 2 = 2 * parityWeight n t := by
  unfold parityWeight
  split_ifs <;> norm_num

/-- The leading left amplitude coefficient `(1 - α) * cos (phaseFn α * t + π / 4)`. -/
def leadAmpL (α t : ℝ) : ℝ := (1 - α) * Real.cos (phaseFn α * t + Real.pi / 4)

/-- The leading right amplitude coefficient combining `α * cos` and `√(1 - 2 * α²) * sin` at the
stationary phase. -/
def leadAmpR (α t : ℝ) : ℝ :=
  α * Real.cos (phaseFn α * t + Real.pi / 4)
    + Real.sqrt (1 - 2 * α ^ 2) * Real.sin (phaseFn α * t + Real.pi / 4)

/-- The two-term oscillatory bracket appearing in `asymProb`. -/
def asymBracket (α t : ℝ) : ℝ :=
  (1 - α) ^ 2 * Real.cos (phaseFn α * t + Real.pi / 4) ^ 2
    + (1 - α ^ 2) * Real.cos (phaseFn α * t + kAlpha α + Real.pi / 4) ^ 2

/-- For `α² < 1/2`, the cosine of `θ + kAlpha α` equals the stated linear combination of `cos θ`
and `sin θ` divided by `-√(1 - α²)`. -/
theorem cos_add_kAlpha {α : ℝ} (hα : α ^ 2 < 1 / 2) (θ : ℝ) :
    Real.cos (θ + kAlpha α)
      = -(α * Real.cos θ + Real.sqrt (1 - 2 * α ^ 2) * Real.sin θ)
          / Real.sqrt (1 - α ^ 2) := by
  have h1 : (0 : ℝ) < 1 - α ^ 2 := by nlinarith
  have hne : Real.sqrt (1 - α ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 h1)
  rw [Real.cos_add, cos_kAlpha hα, sin_kAlpha hα]
  field_simp
  ring

/-- For `α² < 1/2`, the leading right amplitude is a shifted cosine with coefficient `-√(1 -
α²)`. See [NayakVishwanath2000]. -/
theorem leadAmpR_eq {α : ℝ} (hα : α ^ 2 < 1 / 2) (t : ℝ) :
    leadAmpR α t
      = -Real.sqrt (1 - α ^ 2) * Real.cos (phaseFn α * t + kAlpha α + Real.pi / 4) := by
  have h1 : (0 : ℝ) < 1 - α ^ 2 := by nlinarith
  have hne : Real.sqrt (1 - α ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 h1)
  unfold leadAmpR
  rw [show phaseFn α * t + kAlpha α + Real.pi / 4
        = (phaseFn α * t + Real.pi / 4) + kAlpha α by ring]
  rw [cos_add_kAlpha hα]
  field_simp

/-- For `α² < 1/2`, the asymptotic bracket is the sum of the squares of the two leading
amplitudes. See [NayakVishwanath2000]. -/
theorem asymBracket_eq_sq_sum {α : ℝ} (hα : α ^ 2 < 1 / 2) (t : ℝ) :
    asymBracket α t = leadAmpL α t ^ 2 + leadAmpR α t ^ 2 := by
  have hsq : (Real.sqrt (1 - α ^ 2)) ^ 2 = 1 - α ^ 2 :=
    Real.sq_sqrt (by nlinarith)
  unfold asymBracket leadAmpL
  rw [leadAmpR_eq hα t]
  rw [show (-Real.sqrt (1 - α ^ 2)
        * Real.cos (phaseFn α * t + kAlpha α + Real.pi / 4)) ^ 2
      = (Real.sqrt (1 - α ^ 2)) ^ 2
        * Real.cos (phaseFn α * t + kAlpha α + Real.pi / 4) ^ 2 by ring]
  rw [hsq]
  ring

/-- The expression `asymProb` is the parity and curvature prefactor multiplied by `asymBracket`
at `α = n / t`. -/
theorem asymProb_eq_parity_mul_bracket (n : ℤ) (t : ℕ) :
    asymProb n t =
      parityWeight n t
          / (Real.pi * (t : ℝ) * |omegaSecondAtStationary ((n : ℝ) / (t : ℝ))|)
        * asymBracket ((n : ℝ) / (t : ℝ)) (t : ℝ) := by
  simp [asymProb, asymBracket]

/-- In the interior regime `(n / t)² < 1/2`, `asymProb` is its parity and curvature prefactor
times the sum of the two leading amplitude squares. See [NayakVishwanath2000]. -/
theorem asymProb_eq_leadAmp_sq (n : ℤ) (t : ℕ)
    (hα : ((n : ℝ) / (t : ℝ)) ^ 2 < 1 / 2) :
    asymProb n t =
      parityWeight n t
          / (Real.pi * (t : ℝ) * |omegaSecondAtStationary ((n : ℝ) / (t : ℝ))|)
        * (leadAmpL ((n : ℝ) / (t : ℝ)) (t : ℝ) ^ 2
            + leadAmpR ((n : ℝ) / (t : ℝ)) (t : ℝ) ^ 2) := by
  rw [asymProb_eq_parity_mul_bracket, asymBracket_eq_sq_sum hα]

/-- The asymptotic probability expression is nonnegative when `(n / t)² < 1/2`. -/
theorem asymProb_nonneg (n : ℤ) (t : ℕ)
    (hα : ((n : ℝ) / (t : ℝ)) ^ 2 < 1 / 2) :
    0 ≤ asymProb n t := by
  have hL : 0 ≤ leadAmpL ((n : ℝ) / (t : ℝ)) (t : ℝ) ^ 2 := sq_nonneg _
  have hR : 0 ≤ leadAmpR ((n : ℝ) / (t : ℝ)) (t : ℝ) ^ 2 := sq_nonneg _
  rw [asymProb_eq_leadAmp_sq n t hα]
  apply mul_nonneg
  · apply div_nonneg (parityWeight_nonneg n t)
    positivity
  · linarith

/-- The exact probability mass, defined as the sum of two squared complex norms, is nonnegative.
See [NayakVishwanath2000]. -/
theorem probMass_nonneg (n : ℤ) (t : ℕ) : 0 ≤ probMass n t := by
  unfold probMass
  have h1 := Complex.normSq_nonneg (psiL n t)
  have h2 := Complex.normSq_nonneg (psiR n t)
  linarith

/-- The asymptotic bracket is nonnegative for `α² < 1/2`. -/
theorem asymBracket_nonneg {α : ℝ} (hα : α ^ 2 < 1 / 2) (t : ℝ) :
    0 ≤ asymBracket α t := by
  rw [asymBracket_eq_sq_sum hα]
  have := sq_nonneg (leadAmpL α t)
  have := sq_nonneg (leadAmpR α t)
  linarith

/-- The product of the complex exponentials of `z` and `-z` is one. -/
lemma exp_mul_exp_neg (z : ℂ) : Complex.exp z * Complex.exp (-z) = 1 := by
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

/-- Conjugating `exp (-i * k)` for real `k` gives `exp (i * k)`. -/
lemma conj_exp_neg_I_mul (k : ℝ) :
    starRingEnd ℂ (Complex.exp (-(Complex.I * (k : ℂ)))) = Complex.exp (Complex.I * (k : ℂ)) := by
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_I, Complex.conj_ofReal]

/-- Conjugating `exp (i * k)` for real `k` gives `exp (-i * k)`. -/
lemma conj_exp_I_mul (k : ℝ) :
    starRingEnd ℂ (Complex.exp (Complex.I * (k : ℂ))) = Complex.exp (-(Complex.I * (k : ℂ))) := by
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_I, Complex.conj_ofReal]

/-- The conjugate transpose of the Hadamard Fourier kernel multiplied by the kernel is the
identity. See [NayakVishwanath2000]. -/
theorem hadamardKernel_unitary (k : ℝ) :
    Matrix.conjTranspose (hadamardKernel k) * hadamardKernel k = 1 := by
  have hA : Complex.exp (Complex.I * (k : ℂ)) * Complex.exp (-(Complex.I * (k : ℂ))) = 1 :=
    exp_mul_exp_neg _
  have hB : Complex.exp (-(Complex.I * (k : ℂ))) * Complex.exp (Complex.I * (k : ℂ)) = 1 := by
    rw [mul_comm]; exact hA
  have hsne : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = (1 / 2 : ℂ) := by
    rw [← mul_inv]
    have hm : ((Real.sqrt 2 : ℂ)) * ((Real.sqrt 2 : ℂ)) = 2 := by
      have hr : (Real.sqrt 2 : ℝ) * (Real.sqrt 2 : ℝ) = 2 := by
        rw [← sq]; exact Real.sq_sqrt (by norm_num)
      exact_mod_cast hr
    rw [hm]; norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, hadamardKernel,
      conj_exp_neg_I_mul, conj_exp_I_mul, smul_eq_mul]
  all_goals
    first
    | linear_combination ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ * hA
        + ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ * hB + 2 * hsne
    | linear_combination ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ * hA
        - ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ * hB

/-- The first Fourier eigenvalue has squared complex norm one. See [NayakVishwanath2000]. -/
theorem normSq_eigValOne (k : ℝ) : Complex.normSq (eigValOne k) = 1 := by
  rw [Complex.normSq_eq_norm_sq, eigValOne, Complex.norm_exp]
  have hre : (-(Complex.I * (dispersion k : ℂ))).re = 0 := by simp
  rw [hre]
  norm_num

/-- The second Fourier eigenvalue has squared complex norm one. See [NayakVishwanath2000]. -/
theorem normSq_eigValTwo (k : ℝ) : Complex.normSq (eigValTwo k) = 1 := by
  rw [Complex.normSq_eq_norm_sq, eigValTwo, norm_neg, Complex.norm_exp]
  have hre : (Complex.I * (dispersion k : ℂ)).re = 0 := by simp
  rw [hre]
  norm_num

end

end Qatlib.Papers.QWalkLine00.MainResults
