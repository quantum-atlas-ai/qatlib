/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.Rounding.Analytic.GaussianScalarMoments
import Mathlib.MeasureTheory.Integral.Prod
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical NNReal
open MeasureTheory ProbabilityTheory Set Real

namespace Qatlib.Papers.RydbergMaxCut26.Rounding.Laplace

abbrev standard1 : Measure ℝ := gaussianReal 0 1

def noisePrecision (b s : ℝ) : ℝ := 1/2+b*s^2

def noiseShift (t b s x : ℝ) : ℝ := -(b*t*s*x)/noisePrecision b s

def remainingRate (t b s : ℝ) : ℝ := b*t^2/(1+2*b*s^2)

theorem noisePrecision_pos {b : ℝ} (hb : 0≤b) (s : ℝ) : 0<noisePrecision b s := by
  unfold noisePrecision
  nlinarith [mul_nonneg hb (sq_nonneg s)]

theorem noise_complete_square (t b s x z : ℝ) (hb : 0≤b) :
    z^2/2+b*(t*x+s*z)^2=noisePrecision b s*(z-noiseShift t b s x)^2+
      remainingRate t b s*x^2 := by
  have hA := (noisePrecision_pos hb s).ne'
  have hB : 1+2*b*s^2≠0 := by nlinarith [mul_nonneg hb (sq_nonneg s)]
  unfold noiseShift remainingRate
  field_simp
  unfold noisePrecision
  ring

theorem integrable_shifted_quadratic (A m : ℝ) (hA : 0<A) :
    Integrable (fun x : ℝ => Real.exp (-A*(x-m)^2)) := by
  simpa only [Function.comp_def,sub_eq_add_neg] using
    (measurePreserving_add_right volume (-m)).integrable_comp_of_integrable
      (integrable_exp_neg_mul_sq hA)

theorem integral_shifted_quadratic (A m : ℝ) :
    (∫ x : ℝ,Real.exp (-A*(x-m)^2))=Real.sqrt (Real.pi/A) := by
  simpa only [sub_eq_add_neg] using
    (integral_add_right_eq_self (μ:=volume) (fun x : ℝ => Real.exp (-A*x^2)) (-m)).trans
      (integral_gaussian A)

theorem integrable_linear_shifted_quadratic (A m : ℝ) (hA : 0<A) :
    Integrable (fun x : ℝ => Real.exp (-A*(x-m)^2)*x) := by
  have hi := (measurePreserving_add_right volume (-m)).integrable_comp_of_integrable
    (integrable_mul_exp_neg_mul_sq hA)
  have hj := (integrable_shifted_quadratic A m hA).mul_const m
  convert! hi.add hj using 1
  funext x
  dsimp
  ring

theorem conditional_tilt_zero (t b s x : ℝ) (hb : 0≤b) :
    (∫ z : ℝ,Real.exp (-b*(t*x+s*z)^2) ∂standard1)=
      (Real.sqrt (2*Real.pi))⁻¹*Real.exp (-remainingRate t b s*x^2)*
        Real.sqrt (Real.pi/noisePrecision b s) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:ℝ≥0)≠0)]
  have he (z : ℝ) : gaussianPDFReal 0 1 z*Real.exp (-b*(t*x+s*z)^2)=
      (Real.sqrt (2*Real.pi))⁻¹*Real.exp (-remainingRate t b s*x^2)*
        Real.exp (-noisePrecision b s*(z-noiseShift t b s x)^2) := by
    simp only [gaussianPDFReal_def,NNReal.coe_one,mul_one,sub_zero,← Real.exp_add,mul_assoc]
    congr 1
    congr 1
    nlinarith [noise_complete_square t b s x z hb]
  simp_rw [smul_eq_mul,he]
  rw [integral_const_mul,integral_shifted_quadratic]

theorem conditional_tilt_linear (t b s x : ℝ) (hb : 0≤b) :
    (∫ z : ℝ,(t*x+s*z)*Real.exp (-b*(t*x+s*z)^2) ∂standard1)=
      (Real.sqrt (2*Real.pi))⁻¹*Real.exp (-remainingRate t b s*x^2)*
        Real.sqrt (Real.pi/noisePrecision b s)*(t*x+s*noiseShift t b s x) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:ℝ≥0)≠0)]
  have he (z : ℝ) : gaussianPDFReal 0 1 z*((t*x+s*z)*Real.exp (-b*(t*x+s*z)^2))=
      ((Real.sqrt (2*Real.pi))⁻¹*Real.exp (-remainingRate t b s*x^2))*
        (Real.exp (-noisePrecision b s*(z-noiseShift t b s x)^2)*(t*x+s*z)) := by
    have h := noise_complete_square t b s x z hb
    simp only [gaussianPDFReal_def,NNReal.coe_one,mul_one,sub_zero]
    have hexp : Real.exp (-(z^2/2))*Real.exp (-b*(t*x+s*z)^2)=
        Real.exp (-remainingRate t b s*x^2)*Real.exp (-noisePrecision b s*(z-noiseShift t b s x)^2) := by
      rw [← Real.exp_add,← Real.exp_add]
      congr 1
      nlinarith [h]
    calc
      _ = ((Real.sqrt (2*Real.pi))⁻¹*(t*x+s*z))*
          (Real.exp (-(z^2/2))*Real.exp (-b*(t*x+s*z)^2)) := by ring
      _ = _ := by rw [hexp];ring
  simp_rw [smul_eq_mul,he]
  rw [integral_const_mul]
  have he' : (fun z : ℝ => Real.exp (-noisePrecision b s*(z-noiseShift t b s x)^2)*(t*x+s*z))=
      fun z => (t*x)*Real.exp (-noisePrecision b s*(z-noiseShift t b s x)^2)+
        s*(Real.exp (-noisePrecision b s*(z-noiseShift t b s x)^2)*z) := by
    funext z
    ring
  rw [he',integral_add ((integrable_shifted_quadratic _ _ (noisePrecision_pos hb s)).const_mul (t*x))
      ((integrable_linear_shifted_quadratic _ _ (noisePrecision_pos hb s)).const_mul s),
    integral_const_mul,integral_const_mul,integral_shifted_quadratic,
    integral_linear_quadratic _ _ (noisePrecision_pos hb s)]
  ring

end Qatlib.Papers.RydbergMaxCut26.Rounding.Laplace
