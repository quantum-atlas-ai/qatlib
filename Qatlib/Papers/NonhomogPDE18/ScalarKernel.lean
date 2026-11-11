/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic

/-!
# Gaussian Fourier kernel for scalar inversion

Defines diagonal multiplication and modeled inverse amplitudes, then evaluates the Gaussian
Fourier integrals used in scalar inversion. The identity `fourier_kernel_identity` expresses the
reciprocal of a nonzero real parameter as an iterated integral. See [ArrazolaEtAl2019].

## Main statements

* `modeledInverse_solves`: the reciprocal amplitudes solve a nonvanishing diagonal system.
* `fourier_kernel_identity`: the Gaussian Fourier kernel evaluates to the reciprocal parameter.

## References

* [Arrazola et al., 2019][ArrazolaEtAl2019]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace Qatlib.Papers.NonhomogPDE18.ScalarKernel

section Diagonal

variable {ι : Type*}

/-- Pointwise multiplication of a complex vector by the diagonal coefficients `d`. -/
def diagApply (d : ι → ℂ) (v : ι → ℂ) : ι → ℂ := fun i => d i * v i

/-- The amplitudes obtained by multiplying each component of `f` by the reciprocal of the
corresponding component of `a`. -/
def modeledInverseAmplitudes (a f : ι → ℂ) : ι → ℂ := fun i => (a i)⁻¹ * f i

/-- The modeled inverse amplitudes equal application of the diagonal operator with reciprocal
coefficients. -/
theorem modeledInverse_apply (a f : ι → ℂ) :
    modeledInverseAmplitudes a f = diagApply (fun i => (a i)⁻¹) f := rfl

/-- If every diagonal coefficient is nonzero, applying the diagonal operator to the modeled
inverse amplitudes recovers `f`. -/
theorem modeledInverse_solves (a f : ι → ℂ) (ha : ∀ i, a i ≠ 0) :
    diagApply a (modeledInverseAmplitudes a f) = f := by
  funext i
  show a i * ((a i)⁻¹ * f i) = f i
  rw [← mul_assoc, mul_inv_cancel₀ (ha i), one_mul]

/-- For nonzero diagonal coefficients, reciprocal diagonal multiplication is a left inverse of
diagonal multiplication. -/
theorem diagApply_inv_comp (a : ι → ℂ) (ha : ∀ i, a i ≠ 0) :
    diagApply (fun i => (a i)⁻¹) ∘ diagApply a = id := by
  funext v i
  show (a i)⁻¹ * (a i * v i) = v i
  rw [← mul_assoc, inv_mul_cancel₀ (ha i), one_mul]

/-- The modeled inverse amplitudes are given componentwise by `(a i)⁻¹ * f i`. -/
theorem modeledInverse_state (a f : ι → ℂ) :
    modeledInverseAmplitudes a f = fun i => (a i)⁻¹ * f i := rfl

end Diagonal

/-- The Fourier transform of the standard Gaussian at real frequency `u` is sqrt(2π)
exp(-u^2/2). -/
lemma gaussian_fourier (u : ℝ) :
    (∫ y : ℝ, Complex.exp (-(1 / 2 : ℂ) * (y : ℂ) ^ 2) *
        Complex.exp (-Complex.I * (u : ℂ) * (y : ℂ)))
      = (Real.sqrt (2 * Real.pi) : ℂ) * Complex.exp (-(u : ℂ) ^ 2 / 2) := by
  have h := fourierIntegral_gaussian (b := (1 / 2 : ℂ)) (by norm_num : 0 < (1 / 2 : ℂ).re)
    (-(u : ℂ))
  have hfun : (fun y : ℝ => Complex.exp (-(1 / 2 : ℂ) * (y : ℂ) ^ 2) *
        Complex.exp (-Complex.I * (u : ℂ) * (y : ℂ)))
      = fun y : ℝ => Complex.exp (Complex.I * (-(u : ℂ)) * (y : ℂ)) *
          Complex.exp (-(1 / 2 : ℂ) * (y : ℂ) ^ 2) := by
    funext y
    rw [mul_comm]
    congr 2
    ring
  rw [hfun, h]
  have hb : ((Real.pi : ℂ) / (1 / 2 : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hb]
  have hcpow : ((2 * Real.pi : ℝ) : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt (2 * Real.pi) : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
    rw [← Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ 2 * Real.pi) (1 / 2 : ℝ),
      ← Real.sqrt_eq_rpow]
  rw [hcpow]
  have harg : -(-(u : ℂ)) ^ 2 / (4 * (1 / 2 : ℂ)) = -(u : ℂ) ^ 2 / 2 := by ring
  rw [harg]

/-- The Fourier transform of the Gaussian multiplied by its variable is -i u sqrt(2π)
exp(-u^2/2). -/
lemma inner_integral (u : ℝ) :
    (∫ y : ℝ, (y : ℂ) * Complex.exp (-(1 / 2 : ℂ) * (y : ℂ) ^ 2) *
        Complex.exp (-Complex.I * (u : ℂ) * (y : ℂ)))
      = -Complex.I * (u : ℂ) * (Real.sqrt (2 * Real.pi) : ℂ) *
          Complex.exp (-(u : ℂ) ^ 2 / 2) := by
  let b : ℂ := 1 / 2
  let c : ℂ := -Complex.I * (u : ℂ)
  let ufun : ℝ → ℂ := fun y => Complex.exp (-b * (y : ℂ) ^ 2)
  let ufun' : ℝ → ℂ := fun y => -2 * b * (y : ℂ) * Complex.exp (-b * (y : ℂ) ^ 2)
  let vfun : ℝ → ℂ := fun y => Complex.exp (c * (y : ℂ))
  let vfun' : ℝ → ℂ := fun y => c * Complex.exp (c * (y : ℂ))
  have hb : 0 < b.re := by norm_num [b]
  have hderiv_u : ∀ x : ℝ, HasDerivAt ufun (ufun' x) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
    have h2 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ 2) (2 * (x : ℂ)) x := by
      simpa using! h1.pow 2
    have h3 : HasDerivAt (fun y : ℝ => -b * (y : ℂ) ^ 2) (-b * (2 * (x : ℂ))) x :=
      h2.const_mul (-b)
    have h4 : HasDerivAt (fun y : ℝ => Complex.exp (-b * (y : ℂ) ^ 2))
        (Complex.exp (-b * (x : ℂ) ^ 2) * (-b * (2 * (x : ℂ)))) x := h3.cexp
    simpa [ufun, ufun', mul_assoc, mul_comm, mul_left_comm] using h4
  have hderiv_v : ∀ x : ℝ, HasDerivAt vfun (vfun' x) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => c * (y : ℂ)) (c * 1) x :=
      Complex.ofRealCLM.hasDerivAt.const_mul c
    have h2 : HasDerivAt (fun y : ℝ => Complex.exp (c * (y : ℂ)))
        (Complex.exp (c * (x : ℂ)) * (c * 1)) x := h1.cexp
    simpa [vfun, vfun', mul_comm] using h2
  have hq : Integrable (fun y : ℝ => Complex.exp (-b * (y : ℂ) ^ 2 + c * (y : ℂ) + 0)) :=
    integrable_cexp_quadratic hb c 0
  have huv' : Integrable (ufun * vfun') := by
    convert hq.const_mul c using 1
    ext y
    simp only [Pi.mul_apply, ufun, vfun']
    rw [show Complex.exp (-b * (y : ℂ) ^ 2) * (c * Complex.exp (c * (y : ℂ)))
        = c * (Complex.exp (-b * (y : ℂ) ^ 2) * Complex.exp (c * (y : ℂ))) by ring]
    rw [← Complex.exp_add]
    simp
  have hqmul : Integrable (fun y : ℝ =>
      (y : ℂ) * Complex.exp (-b * (y : ℂ) ^ 2 + c * (y : ℂ))) := by
    have hbase : Integrable (fun y : ℝ => (y : ℝ) * Real.exp (-b.re * y ^ 2)) :=
      integrable_mul_exp_neg_mul_sq hb
    have hnorm_eq : (fun y : ℝ =>
        ‖(y : ℂ) * Complex.exp (-b * (y : ℂ) ^ 2 + c * (y : ℂ))‖)
        = fun y : ℝ => ‖(y : ℝ) * Real.exp (-b.re * y ^ 2)‖ := by
      funext y
      rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
      have hre : (-b * (y : ℂ) ^ 2 + c * (y : ℂ)).re = -b.re * y ^ 2 := by
        simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, c, b,
          pow_two]
      rw [hre, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hnorm : Integrable (fun y : ℝ =>
        ‖(y : ℂ) * Complex.exp (-b * (y : ℂ) ^ 2 + c * (y : ℂ))‖) := by
      rw [hnorm_eq]
      exact hbase.norm
    exact hnorm.mono' (by fun_prop) (ae_of_all _ fun y => le_rfl)
  have hu'v : Integrable (ufun' * vfun) := by
    convert hqmul.const_mul (-2 * b) using 1
    ext y
    simp only [Pi.mul_apply, ufun', vfun]
    rw [show -2 * b * (y : ℂ) * Complex.exp (-b * (y : ℂ) ^ 2) * Complex.exp (c * (y : ℂ))
        = (-2 * b) * ((y : ℂ) *
            (Complex.exp (-b * (y : ℂ) ^ 2) * Complex.exp (c * (y : ℂ)))) by ring]
    rw [← Complex.exp_add]
  have huv : Integrable (ufun * vfun) := by
    convert hq using 1
    ext y
    simp only [Pi.mul_apply, ufun, vfun]
    rw [← Complex.exp_add]
    simp
  have hIBP := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := ufun) (v := vfun) (u' := ufun') (v' := vfun')
    (fun x _ => hderiv_u x) (fun x _ => hderiv_v x) huv' hu'v huv
  have hleft : (∫ y : ℝ, ufun y * vfun' y) = c * (∫ y : ℝ, ufun y * vfun y) := by
    rw [show (fun y : ℝ => ufun y * vfun' y) = fun y : ℝ => c * (ufun y * vfun y) by
      funext y
      simp only [vfun']
      ring]
    rw [integral_const_mul]
  have hright : (∫ y : ℝ, ufun' y * vfun y) =
      (-2 * b) * (∫ y : ℝ, (y : ℂ) * ufun y * vfun y) := by
    rw [show (fun y : ℝ => ufun' y * vfun y) =
        fun y : ℝ => (-2 * b) * ((y : ℂ) * ufun y * vfun y) by
      funext y
      simp only [ufun']
      ring]
    rw [integral_const_mul]
  have hG : (∫ y : ℝ, ufun y * vfun y) =
      (Real.sqrt (2 * Real.pi) : ℂ) * Complex.exp (-(u : ℂ) ^ 2 / 2) := by
    simpa [ufun, vfun, b, c, mul_assoc] using gaussian_fourier u
  have hI : (∫ y : ℝ, (y : ℂ) * ufun y * vfun y) =
      -Complex.I * (u : ℂ) * (Real.sqrt (2 * Real.pi) : ℂ) *
        Complex.exp (-(u : ℂ) ^ 2 / 2) := by
    have h1 : c * (∫ y : ℝ, ufun y * vfun y) =
        -((-2 * b) * (∫ y : ℝ, (y : ℂ) * ufun y * vfun y)) := by
      rw [← hleft, hIBP, hright]
    have h2b : (-2 * b) = -1 := by rw [show b = (1 / 2 : ℂ) from rfl]; ring
    rw [h2b] at h1
    have hIfinal : (∫ y : ℝ, (y : ℂ) * ufun y * vfun y) =
        c * (∫ y : ℝ, ufun y * vfun y) := by
      rw [h1]
      ring
    rw [hIfinal, hG, show c = -Complex.I * (u : ℂ) from rfl]
    ring
  simpa [ufun, vfun, b, c, mul_assoc] using hI

/-- The Fourier integral with Gaussian exponent -y^2/2 and an additional factor `y` equals -i u
sqrt(2π) exp(-u^2/2). -/
lemma inner_integral' (u : ℝ) :
    (∫ y : ℝ, (y : ℂ) * Complex.exp (-(y : ℂ) ^ 2 / 2) *
        Complex.exp (-Complex.I * (u : ℂ) * (y : ℂ)))
      = -Complex.I * (u : ℂ) * (Real.sqrt (2 * Real.pi) : ℂ) *
          Complex.exp (-(u : ℂ) ^ 2 / 2) := by
  have h := inner_integral u
  have harg : ∀ z : ℂ, -z ^ 2 / 2 = -(1 / 2 : ℂ) * z ^ 2 := fun z => by ring
  simpa only [harg] using h

/-- For nonzero real `a`, the integral of x exp(-a^2 x^2/2) over the positive half-line equals
the reciprocal of a^2. -/
lemma outer_integral (a : ℝ) (ha : a ≠ 0) :
    (∫ x : ℝ in Set.Ioi 0, (x : ℂ) * Complex.exp (-((a : ℂ) ^ 2 / 2) * (x : ℂ) ^ 2))
      = ((a : ℂ) ^ 2)⁻¹ := by
  have hb : ((a : ℂ) ^ 2 / 2) = ((a ^ 2 / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  have ha2 : 0 < ((a : ℂ) ^ 2 / 2).re := by
    rw [hb, Complex.ofReal_re]
    have hpos : 0 < a ^ 2 := sq_pos_of_ne_zero ha
    positivity
  have h := integral_mul_cexp_neg_mul_sq (b := (a : ℂ) ^ 2 / 2) ha2
  rw [show 2 * ((a : ℂ) ^ 2 / 2) = (a : ℂ) ^ 2 by ring] at h
  exact h

/-- For nonzero real `a`, the Gaussian iterated Fourier kernel with prefactor i/sqrt(2π)
evaluates to the complex reciprocal of `a`. See [ArrazolaEtAl2019]. -/
theorem fourier_kernel_identity {a : ℝ} (ha : a ≠ 0) :
    Complex.I / ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) *
      (∫ x : ℝ in Set.Ioi 0, ∫ y : ℝ,
        (y : ℂ) * Complex.exp (-(y : ℂ) ^ 2 / 2) *
          Complex.exp (-Complex.I * (a : ℂ) * (x : ℂ) * (y : ℂ)))
      = (a : ℂ)⁻¹ := by
  have hinner : ∀ x : ℝ,
      (∫ y : ℝ, (y : ℂ) * Complex.exp (-(y : ℂ) ^ 2 / 2) *
          Complex.exp (-Complex.I * (a : ℂ) * (x : ℂ) * (y : ℂ)))
        = -Complex.I * ((a * x : ℝ) : ℂ) * (Real.sqrt (2 * Real.pi) : ℂ) *
            Complex.exp (-((a * x : ℝ) : ℂ) ^ 2 / 2) := by
    intro x
    simpa [Complex.ofReal_mul, mul_assoc] using inner_integral' (a * x)
  have hcinner : (∫ x : ℝ in Set.Ioi 0,
        ∫ y : ℝ, (y : ℂ) * Complex.exp (-(y : ℂ) ^ 2 / 2) *
          Complex.exp (-Complex.I * (a : ℂ) * (x : ℂ) * (y : ℂ)))
      = ∫ x : ℝ in Set.Ioi 0, -Complex.I * ((a * x : ℝ) : ℂ) *
          (Real.sqrt (2 * Real.pi) : ℂ) * Complex.exp (-((a * x : ℝ) : ℂ) ^ 2 / 2) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    exact hinner x
  rw [hcinner]
  have hstep : ∀ x : ℝ,
      -Complex.I * ((a * x : ℝ) : ℂ) * (Real.sqrt (2 * Real.pi) : ℂ) *
          Complex.exp (-((a * x : ℝ) : ℂ) ^ 2 / 2)
        = (-Complex.I * (Real.sqrt (2 * Real.pi) : ℂ) * (a : ℂ)) *
            ((x : ℂ) * Complex.exp (-((a : ℂ) ^ 2 / 2) * (x : ℂ) ^ 2)) := by
    intro x
    rw [Complex.ofReal_mul]
    have he : -(((a : ℂ) * (x : ℂ)) ^ 2) / 2 = -((a : ℂ) ^ 2 / 2) * (x : ℂ) ^ 2 := by
      ring
    rw [he]
    ring
  have houter :
      (∫ x : ℝ in Set.Ioi 0, -Complex.I * ((a * x : ℝ) : ℂ) *
          (Real.sqrt (2 * Real.pi) : ℂ) * Complex.exp (-((a * x : ℝ) : ℂ) ^ 2 / 2))
        = (-Complex.I * (Real.sqrt (2 * Real.pi) : ℂ) * (a : ℂ)) *
            ((a : ℂ) ^ 2)⁻¹ := by
    calc
      (∫ x : ℝ in Set.Ioi 0, -Complex.I * ((a * x : ℝ) : ℂ) *
          (Real.sqrt (2 * Real.pi) : ℂ) * Complex.exp (-((a * x : ℝ) : ℂ) ^ 2 / 2))
          = ∫ x : ℝ in Set.Ioi 0, (-Complex.I * (Real.sqrt (2 * Real.pi) : ℂ) * (a : ℂ)) *
              ((x : ℂ) * Complex.exp (-((a : ℂ) ^ 2 / 2) * (x : ℂ) ^ 2)) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro x _
            exact hstep x
      _ = (-Complex.I * (Real.sqrt (2 * Real.pi) : ℂ) * (a : ℂ)) *
            ∫ x : ℝ in Set.Ioi 0, (x : ℂ) * Complex.exp (-((a : ℂ) ^ 2 / 2) * (x : ℂ) ^ 2) := by
            rw [integral_const_mul]
      _ = (-Complex.I * (Real.sqrt (2 * Real.pi) : ℂ) * (a : ℂ)) * ((a : ℂ) ^ 2)⁻¹ := by
            rw [outer_integral a ha]
  rw [houter]
  have hsqrt : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  field_simp
  rw [Complex.I_sq]
  ring

end Qatlib.Papers.NonhomogPDE18.ScalarKernel
