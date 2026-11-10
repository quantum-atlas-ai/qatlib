/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkLine00.MainResults.WalkModel.SpectralFacts
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Complex.Trigonometric
set_option warningAsError false

namespace Qatlib.Papers.QWalkLine00.MainResults
set_option autoImplicit false
open Real
noncomputable section

lemma exp_I_mul (x : ℝ) :
    Complex.exp (Complex.I * (x : ℂ)) = (Real.cos x : ℂ) + (Real.sin x : ℂ) * Complex.I := by
  rw [show Complex.I * (x : ℂ) = ((x : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.exp_ofReal_mul_I]

lemma exp_neg_I_mul (x : ℝ) :
    Complex.exp (-(Complex.I * (x : ℂ))) = (Real.cos x : ℂ) - (Real.sin x : ℂ) * Complex.I := by
  rw [show -(Complex.I * (x : ℂ)) = ((-x : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.exp_ofReal_mul_I]; rw [Real.cos_neg, Real.sin_neg]; push_cast; ring

def eigValOne (k : ℝ) : ℂ := Complex.exp (-(Complex.I * (dispersion k : ℂ)))

def eigValTwo (k : ℝ) : ℂ := -Complex.exp (Complex.I * (dispersion k : ℂ))

def eigOneTwo (k : ℝ) : ℂ := (Real.sqrt 2 : ℂ) * eigValOne k - Complex.exp (-(Complex.I * (k : ℂ)))

def eigTwoTwo (k : ℝ) : ℂ := -((Real.sqrt 2 : ℂ) * Complex.exp (Complex.I * (dispersion k : ℂ)))
  - Complex.exp (-(Complex.I * (k : ℂ)))

def eigVecOne (k : ℝ) : Fin 2 → ℂ := fun i =>
  if i = 0 then Complex.exp (-(Complex.I * (k : ℂ))) else eigOneTwo k

def eigVecTwo (k : ℝ) : Fin 2 → ℂ := fun i =>
  if i = 0 then Complex.exp (-(Complex.I * (k : ℂ))) else eigTwoTwo k

lemma sqrtTwo_ne_zero_c : (Real.sqrt 2 : ℂ) ≠ 0 := by
  have h : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  exact_mod_cast ne_of_gt h

lemma sqrtTwo_sq_c : ((Real.sqrt 2 : ℂ)) ^ 2 = 2 := by
  have h : (0 : ℝ) ≤ 2 := by norm_num
  have := Real.sq_sqrt h
  exact_mod_cast this

theorem eigen_one_first (k : ℝ) :
    Matrix.mulVec (hadamardKernel k) (eigVecOne k) 0 = eigValOne k * eigVecOne k 0 := by
  simp [Matrix.mulVec, Fin.sum_univ_two, hadamardKernel, eigVecOne, eigOneTwo, eigValOne]
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := sqrtTwo_ne_zero_c
  field_simp
  ring

theorem eigen_one_second (k : ℝ) :
    Matrix.mulVec (hadamardKernel k) (eigVecOne k) 1 = eigValOne k * eigVecOne k 1 := by
  simp [Matrix.mulVec, Fin.sum_univ_two, hadamardKernel, eigVecOne, eigOneTwo, eigValOne]
  simp only [exp_I_mul, exp_neg_I_mul]
  have hsin : Real.sin (dispersion k) = Real.sin k / Real.sqrt 2 := sin_dispersion k
  have hcos : Real.cos (dispersion k) = Real.sqrt (1 + Real.cos k ^ 2) / Real.sqrt 2 :=
      cos_dispersion k
  rw [hsin, hcos]
  have hsq : (Real.sqrt (1 + Real.cos k ^ 2)) ^ 2 = 1 + Real.cos k ^ 2 :=
      Real.sq_sqrt (by positivity)
  have hsq2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  apply Complex.ext
  · simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    field_simp
    ring_nf
    try rw [hsq2]
    try rw [hsq]
    try ring
    try nlinarith [Real.sin_sq_add_cos_sq k]
  · simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    field_simp
    ring_nf
    try rw [hsq2]
    try rw [hsq]
    try ring
    try nlinarith [Real.sin_sq_add_cos_sq k]

theorem eigen_two_first (k : ℝ) :
    Matrix.mulVec (hadamardKernel k) (eigVecTwo k) 0 = eigValTwo k * eigVecTwo k 0 := by
  simp [Matrix.mulVec, Fin.sum_univ_two, hadamardKernel, eigVecTwo, eigTwoTwo,
    eigValTwo, eigValOne]
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := sqrtTwo_ne_zero_c
  field_simp
  ring

theorem eigen_two_second (k : ℝ) :
    Matrix.mulVec (hadamardKernel k) (eigVecTwo k) 1 = eigValTwo k * eigVecTwo k 1 := by
  simp [Matrix.mulVec, Fin.sum_univ_two, hadamardKernel, eigVecTwo, eigTwoTwo,
    eigValTwo, eigValOne]
  simp only [exp_I_mul, exp_neg_I_mul]
  have hsin : Real.sin (dispersion k) = Real.sin k / Real.sqrt 2 := sin_dispersion k
  have hcos : Real.cos (dispersion k) = Real.sqrt (1 + Real.cos k ^ 2) / Real.sqrt 2 :=
      cos_dispersion k
  rw [hsin, hcos]
  have hsq : (Real.sqrt (1 + Real.cos k ^ 2)) ^ 2 = 1 + Real.cos k ^ 2 :=
      Real.sq_sqrt (by positivity)
  have hsq2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  apply Complex.ext
  · simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    field_simp
    ring_nf
    try rw [hsq2]
    try rw [hsq]
    try ring
    try nlinarith [Real.sin_sq_add_cos_sq k]
  · simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    field_simp
    ring_nf
    try rw [hsq2]
    try rw [hsq]
    try ring
    try nlinarith [Real.sin_sq_add_cos_sq k]

def ampL (k : ℝ) : ℂ := (((1 + Real.cos k / Real.sqrt (1 + Real.cos k ^ 2)) / 2 : ℝ) : ℂ)

def ampLp (k : ℝ) : ℂ := (((1 - Real.cos k / Real.sqrt (1 + Real.cos k ^ 2)) / 2 : ℝ) : ℂ)

def ampR (k : ℝ) : ℂ :=
  (((2 * Real.sqrt (1 + Real.cos k ^ 2))⁻¹ : ℝ) : ℂ) * Complex.exp (Complex.I * (k : ℂ))

theorem coef_one (k : ℝ) :
    (Real.sqrt 2 : ℂ)⁻¹ * Complex.exp (-(Complex.I * (k : ℂ))) * (ampL k + ampR k)
      = ampL k * eigValOne k := by
  simp only [ampL, ampLp, ampR, eigValOne, eigValTwo, exp_I_mul, exp_neg_I_mul]
  have hsin : Real.sin (dispersion k) = Real.sin k / Real.sqrt 2 := sin_dispersion k
  have hcos : Real.cos (dispersion k) = Real.sqrt (1 + Real.cos k ^ 2) / Real.sqrt 2 :=
      cos_dispersion k
  rw [hsin, hcos]
  have hsq : (Real.sqrt (1 + Real.cos k ^ 2)) ^ 2 = 1 + Real.cos k ^ 2 :=
      Real.sq_sqrt (by positivity)
  have hsq2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  apply Complex.ext
  · simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    field_simp
    ring_nf
    try rw [hsq2]
    try rw [hsq]
    try ring
    try nlinarith [Real.sin_sq_add_cos_sq k, hsq]
  · simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    field_simp
    ring_nf
    try rw [hsq2]
    try rw [hsq]
    try ring
    try nlinarith [Real.sin_sq_add_cos_sq k, hsq]

theorem coef_two (k : ℝ) :
    (Real.sqrt 2 : ℂ)⁻¹ * Complex.exp (-(Complex.I * (k : ℂ))) * (ampLp k - ampR k)
      = ampLp k * eigValTwo k := by
  simp only [ampL, ampLp, ampR, eigValOne, eigValTwo, exp_I_mul, exp_neg_I_mul]
  have hsin : Real.sin (dispersion k) = Real.sin k / Real.sqrt 2 := sin_dispersion k
  have hcos : Real.cos (dispersion k) = Real.sqrt (1 + Real.cos k ^ 2) / Real.sqrt 2 :=
      cos_dispersion k
  rw [hsin, hcos]
  have hsq : (Real.sqrt (1 + Real.cos k ^ 2)) ^ 2 = 1 + Real.cos k ^ 2 :=
      Real.sq_sqrt (by positivity)
  have hsq2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  apply Complex.ext
  · simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    field_simp
    ring_nf
    try rw [hsq2]
    try rw [hsq]
    try ring
    try nlinarith [Real.sin_sq_add_cos_sq k, hsq]
  · simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    field_simp
    ring_nf
    try rw [hsq2]
    try rw [hsq]
    try ring
    try nlinarith [Real.sin_sq_add_cos_sq k, hsq]

theorem coef_three (k : ℝ) :
    (Real.sqrt 2 : ℂ)⁻¹ * Complex.exp (Complex.I * (k : ℂ)) * (ampL k - ampR k)
      = ampR k * eigValOne k := by
  simp only [ampL, ampLp, ampR, eigValOne, eigValTwo, exp_I_mul, exp_neg_I_mul]
  have hsin : Real.sin (dispersion k) = Real.sin k / Real.sqrt 2 := sin_dispersion k
  have hcos : Real.cos (dispersion k) = Real.sqrt (1 + Real.cos k ^ 2) / Real.sqrt 2 :=
      cos_dispersion k
  rw [hsin, hcos]
  have hsq : (Real.sqrt (1 + Real.cos k ^ 2)) ^ 2 = 1 + Real.cos k ^ 2 :=
      Real.sq_sqrt (by positivity)
  have hsq2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  apply Complex.ext
  · simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    field_simp
    ring_nf
    try rw [hsq2]
    try rw [hsq]
    try ring
    try nlinarith [Real.sin_sq_add_cos_sq k, hsq]
  · simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    field_simp
    ring_nf
    try rw [hsq2]
    try rw [hsq]
    try ring
    try nlinarith [Real.sin_sq_add_cos_sq k, hsq]

theorem coef_four (k : ℝ) :
    (Real.sqrt 2 : ℂ)⁻¹ * Complex.exp (Complex.I * (k : ℂ)) * (ampLp k + ampR k)
      = -(ampR k * eigValTwo k) := by
  simp only [ampL, ampLp, ampR, eigValOne, eigValTwo, exp_I_mul, exp_neg_I_mul]
  have hsin : Real.sin (dispersion k) = Real.sin k / Real.sqrt 2 := sin_dispersion k
  have hcos : Real.cos (dispersion k) = Real.sqrt (1 + Real.cos k ^ 2) / Real.sqrt 2 :=
      cos_dispersion k
  rw [hsin, hcos]
  have hsq : (Real.sqrt (1 + Real.cos k ^ 2)) ^ 2 = 1 + Real.cos k ^ 2 :=
      Real.sq_sqrt (by positivity)
  have hsq2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  apply Complex.ext
  · simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    field_simp
    ring_nf
    try rw [hsq2]
    try rw [hsq]
    try ring
    try nlinarith [Real.sin_sq_add_cos_sq k, hsq]
  · simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    field_simp
    ring_nf
    try rw [hsq2]
    try rw [hsq]
    try ring
    try nlinarith [Real.sin_sq_add_cos_sq k, hsq]

def fourierAmp (k : ℝ) (t : ℕ) : Fin 2 → ℂ := fun i =>
  if i = 0 then ampL k * eigValOne k ^ t + ampLp k * eigValTwo k ^ t
  else ampR k * eigValOne k ^ t - ampR k * eigValTwo k ^ t

def initFourier : Fin 2 → ℂ := fun i => if i = 0 then 1 else 0

theorem fourierAmp_zero (k : ℝ) : fourierAmp k 0 = initFourier := by
  funext i
  fin_cases i
  · simp [fourierAmp, initFourier, ampL, ampLp]
    ring
  · simp [fourierAmp, initFourier]

theorem fourierAmp_succ (k : ℝ) (t : ℕ) :
    Matrix.mulVec (hadamardKernel k) (fourierAmp k t) = fourierAmp k (t + 1) := by
  funext i
  fin_cases i
  · simp [fourierAmp, Matrix.mulVec, Fin.sum_univ_two, hadamardKernel, pow_succ]
    linear_combination (eigValOne k ^ t) * coef_one k + (eigValTwo k ^ t) * coef_two k
  · simp [fourierAmp, Matrix.mulVec, Fin.sum_univ_two, hadamardKernel, pow_succ]
    linear_combination (eigValOne k ^ t) * coef_three k + (eigValTwo k ^ t) * coef_four k

theorem hadamardKernel_pow_e1 (k : ℝ) (t : ℕ) :
    Matrix.mulVec ((hadamardKernel k) ^ t) initFourier = fourierAmp k t := by
  induction t with
  | zero => simp [pow_zero, Matrix.one_mulVec, fourierAmp_zero]
  | succ t ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, fourierAmp_succ]

end
end Qatlib.Papers.QWalkLine00.MainResults
