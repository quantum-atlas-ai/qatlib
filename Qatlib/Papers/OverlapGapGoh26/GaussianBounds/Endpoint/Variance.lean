/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint.Scalar
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical RealInnerProductSpace
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.RawInput
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.RawMoments
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.TensorMoments
namespace Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint

def spinCoefficient (r T : ℕ) : ℝ :=
  4*Real.sqrt (T:ℝ)*(2+2*(r:ℝ)*Real.sqrt (T:ℝ))^T

theorem test_gradient_polynomial {r N T : ℕ} (hr : 0<r) (hN : 0<N) (s : ℕ→ℝ)
    (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1) (v : EuclideanSpace ℝ (Fin N))
    (hv : ‖v‖≤Real.sqrt (N:ℝ)) (x : Input r N) :
    ‖fderiv ℝ (test (r:=r) s T v) x‖^2≤
      ((spinCoefficient r T)^2/(N:ℝ))*(1+normScale x)^(2*T) := by
  let K := normScale x
  let A : ℝ := 2+2*(r:ℝ)*Real.sqrt (T:ℝ)
  have hK : 0≤K := by dsimp [K,normScale];positivity
  have hb : 2+2*K*(r:ℝ)*Real.sqrt (T:ℝ)≤A*(1+K) := by
    have hrR : (0:ℝ)≤r := Nat.cast_nonneg r
    dsimp [A]
    nlinarith [mul_nonneg hrR (Real.sqrt_nonneg (T:ℝ))]
  have hp := pow_le_pow_left₀ (by positivity : 0≤2+2*K*(r:ℝ)*Real.sqrt (T:ℝ)) hb T
  rw [mul_pow] at hp
  have h := (test_fderiv_bound hr hN s hs v hv x).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity : 0≤4*Real.sqrt (T:ℝ))) (Real.sqrt_nonneg (N:ℝ)))
  have hbudget : 4*Real.sqrt (T:ℝ)*(A^T*(1+K)^T)/Real.sqrt (N:ℝ)=
      (spinCoefficient r T/Real.sqrt (N:ℝ))*(1+normScale x)^T := by dsimp [A,K,spinCoefficient];ring
  rw [hbudget] at h
  have hh := pow_le_pow_left₀ (norm_nonneg _) h 2
  refine hh.trans_eq ?_
  rw [mul_pow,div_pow,Real.sq_sqrt (Nat.cast_nonneg N),← pow_mul,show T*2=2*T by omega]

theorem test_gradient_integrable {r N T : ℕ} (hr : 0<r) (hN : 0<N) (s : ℕ→ℝ)
    (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1) (v : EuclideanSpace ℝ (Fin N))
    (hv : ‖v‖≤Real.sqrt (N:ℝ)) :
    Integrable (fun x:Input r N=>‖fderiv ℝ (test s T v) x‖^2) (stdGaussian (Input r N)) := by
  have hp := (input_moment_bound hr hN (2*T)).1.const_mul ((spinCoefficient r T)^2/(N:ℝ))
  have hc : Continuous (fun x:Input r N=>‖fderiv ℝ (test s T v) x‖^2) := by
    have := (test_smooth (r:=r) s T v).continuous_fderiv (by simp)
    fun_prop
  apply hp.mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x=>by
    simpa only [Real.norm_eq_abs,abs_pow,sq_abs] using test_gradient_polynomial hr hN s hs v hv x

theorem test_gradient_integral_bound {r N T : ℕ} (hr : 0<r) (hN : 0<N) (s : ℕ→ℝ)
    (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1) (v : EuclideanSpace ℝ (Fin N))
    (hv : ‖v‖≤Real.sqrt (N:ℝ)) :
    (∫ x:Input r N,‖fderiv ℝ (test s T v) x‖^2 ∂stdGaussian (Input r N))≤
      ((spinCoefficient r T)^2/(N:ℝ))*uniformMomentConstant r (2*T) := by
  have hp := input_moment_bound hr hN (2*T)
  calc
    _ ≤ ∫ x:Input r N,((spinCoefficient r T)^2/(N:ℝ))*(1+normScale x)^(2*T) ∂stdGaussian (Input r N) :=
      integral_mono (test_gradient_integrable hr hN s hs v hv) (hp.1.const_mul _)
        (fun x=>test_gradient_polynomial hr hN s hs v hv x)
    _ = _ := by rw [integral_const_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hp.2 (by positivity)

def endpointConstant (r T : ℕ) : ℝ :=
  (Real.pi^2/8)*(spinCoefficient r T)^2*uniformMomentConstant r (2*T)

theorem test_variance_uniform {r N T : ℕ} (hr : 0<r) (hN : 0<N) (s : ℕ→ℝ)
    (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1) (v : EuclideanSpace ℝ (Fin N))
    (hv : ‖v‖≤Real.sqrt (N:ℝ)) :
    variance (test (r:=r) s T v) (stdGaussian (Input r N))≤endpointConstant r T/(N:ℝ) := by
  have h := Qatlib.Foundations.ProbabilityCore.GaussPoincare.Poincare.c1_gaussian_poincare_gradient
    (test s T v) ((test_smooth s T v).of_le (by simp)) (test_memLp s T v)
    (test_gradient_integrable hr hN s hs v hv)
  refine h.trans ?_
  exact (mul_le_mul_of_nonneg_left (test_gradient_integral_bound hr hN s hs v hv)
    (by positivity : (0:ℝ)≤Real.pi^2/8)).trans_eq (by unfold endpointConstant;ring)

theorem test_second_moment {r N T : ℕ} (hr : Odd r) (hN : 0<N) (s : ℕ→ℝ)
    (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1) (v : EuclideanSpace ℝ (Fin N))
    (hv : ‖v‖≤Real.sqrt (N:ℝ)) :
    (∫ x:Input r N,(test s T v x)^2 ∂stdGaussian (Input r N))≤endpointConstant r T/(N:ℝ) := by
  have he := variance_eq_sub (test_memLp (r:=r) s T v)
  rw [test_mean_zero hr,zero_pow (by norm_num : (2:ℕ)≠0),sub_zero] at he
  simp only [Pi.pow_apply] at he
  rw [← he]
  exact test_variance_uniform hr.pos hN s hs v hv
end Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint
