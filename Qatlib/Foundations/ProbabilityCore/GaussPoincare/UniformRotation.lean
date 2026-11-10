/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.ProbabilityCore.GaussPoincare.Poincare
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical NNReal
namespace Qatlib.Foundations.ProbabilityCore.GaussPoincare.UniformRotation
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def angularEnergy (f : E→ℝ) (z : E×E) : ℝ :=
  (Real.pi/2)*(∫ θ in (0:ℝ)..Real.pi/2,
    ((fderiv ℝ f (ContinuousLinearMap.rotation θ z).1) (ContinuousLinearMap.rotation θ z).2)^2)

theorem angularEnergy_nonneg (f : E→ℝ) (z : E×E) : 0≤angularEnergy f z := by
  unfold angularEnergy
  exact mul_nonneg (by positivity)
      (intervalIntegral.integral_nonneg_of_forall (by positivity) (fun θ => sq_nonneg _))

theorem rotation_uniform_square (f : E→ℝ) (hf : ContDiff ℝ 1 f) (z : E×E)
    (θ : ℝ) (hθ : θ∈Set.Icc (0:ℝ) (Real.pi/2)) :
    (f (ContinuousLinearMap.rotation θ z).1-f z.1)^2≤angularEnergy f z := by
  let g :=
      fun a : ℝ => (fderiv ℝ f (ContinuousLinearMap.rotation a z).1) (ContinuousLinearMap.rotation a z).2
  have hc : Continuous g := by
    apply (hf.continuous_fderiv_apply (by norm_num)).comp
    simp only [ContinuousLinearMap.rotation_apply]
    fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=θ)
    (fun a _ => Rotation.observable_rotation_deriv f z a ((hf.differentiable (by norm_num)).differentiableAt))
    (hc.intervalIntegrable 0 θ)
  have hzero : f (ContinuousLinearMap.rotation 0 z).1=f z.1 := by
    simp [ContinuousLinearMap.rotation_apply]
  rw [hzero] at hftc
  by_cases ht : θ=0
  · subst θ
    rw [hzero,sub_self,pow_two,mul_zero]
    exact angularEnergy_nonneg f z
  have htpos : 0<θ := lt_of_le_of_ne hθ.1 (Ne.symm ht)
  have hs := AngleIntegral.angle_square_cauchy g hc θ htpos
  rw [hftc] at hs
  have hmono : (∫ a in (0:ℝ)..θ,(g a)^2)≤∫ a in (0:ℝ)..Real.pi/2,(g a)^2 :=
    intervalIntegral.integral_mono_interval le_rfl hθ.1 hθ.2
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) ((hc.pow 2).intervalIntegrable _ _)
  have hint : 0≤∫ a in (0:ℝ)..θ,(g a)^2 :=
    intervalIntegral.integral_nonneg_of_forall hθ.1 (fun _ => sq_nonneg _)
  exact hs.trans (mul_le_mul hθ.2 hmono hint (by positivity))

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem angularEnergy_integrable (f : E→ℝ) (hf : ContDiff ℝ 1 f)
    (hgrad : Integrable (fun x:E=>‖fderiv ℝ f x‖^2) (stdGaussian E)) :
    Integrable (angularEnergy f) ((stdGaussian E).prod (stdGaussian E)) := by
  unfold angularEnergy
  simp only [intervalIntegral.integral_of_le (by positivity : (0:ℝ)≤Real.pi/2)]
  exact (Poincare.angle_gradient_integrable f hf hgrad).integral_prod_right.const_mul _

theorem integral_angularEnergy (f : E→ℝ) (hf : ContDiff ℝ 1 f)
    (hgrad : Integrable (fun x:E=>‖fderiv ℝ f x‖^2) (stdGaussian E)) :
    (∫ z:E×E,angularEnergy f z ∂((stdGaussian E).prod (stdGaussian E)))=
      (Real.pi^2/4)*(∫ x,‖fderiv ℝ f x‖^2 ∂stdGaussian E) := by
  unfold angularEnergy
  rw [integral_const_mul]
  simp only [intervalIntegral.integral_of_le (by positivity : (0:ℝ)≤Real.pi/2)]
  rw [← integral_integral_swap (Poincare.angle_gradient_integrable f hf hgrad)]
  simp_rw [Poincare.rotated_gradient_square f hf hgrad]
  rw [← intervalIntegral.integral_of_le (by positivity : (0:ℝ)≤Real.pi/2),intervalIntegral.integral_const]
  simp only [sub_zero,smul_eq_mul]
  ring

theorem continuum_rotation_tail (f : E→ℝ) (hf : ContDiff ℝ 1 f)
    (hgrad : Integrable (fun x:E=>‖fderiv ℝ f x‖^2) (stdGaussian E)) (ε : ℝ) (hε : 0<ε) :
    ((stdGaussian E).prod (stdGaussian E)).real
      {z | ∃ θ∈Set.Icc (0:ℝ) (Real.pi/2),ε≤|f (ContinuousLinearMap.rotation θ z).1-f z.1|}≤
      (Real.pi^2/4)*(∫ x,‖fderiv ℝ f x‖^2 ∂stdGaussian E)/ε^2 := by
  have hsub : {z:E×E | ∃ θ∈Set.Icc (0:ℝ) (Real.pi/2),ε≤|f (ContinuousLinearMap.rotation θ z).1-f z.1|}⊆
      {z | ε^2≤angularEnergy f z} := by
    rintro z ⟨θ,hθ,h⟩
    have hsq : ε^2≤(f (ContinuousLinearMap.rotation θ z).1-f z.1)^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ hε.le h 2
    exact hsq.trans (rotation_uniform_square f hf z θ hθ)
  refine (measureReal_mono hsub).trans ?_
  have hm := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall (angularEnergy_nonneg f))
    (angularEnergy_integrable f hf hgrad) (ε^2)
  rw [integral_angularEnergy f hf hgrad] at hm
  exact (le_div_iff₀ (sq_pos_of_pos hε)).mpr (by simpa only [mul_comm] using hm)

end Qatlib.Foundations.ProbabilityCore.GaussPoincare.UniformRotation
