/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.ProbabilityCore.GaussPoincare.Directional
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory
namespace Qatlib.Foundations.ProbabilityCore.GaussPoincare.AngleIntegral

theorem angle_square_cauchy (g : ℝ→ℝ) (hg : Continuous g) (b : ℝ) (hb : 0<b) :
    (∫ θ in (0:ℝ)..b,g θ)^2≤b*(∫ θ in (0:ℝ)..b,(g θ)^2) := by
  let I := ∫ θ in (0:ℝ)..b,g θ
  let J := ∫ θ in (0:ℝ)..b,(g θ)^2
  let c := I/b
  have hpos : 0≤∫ θ in (0:ℝ)..b,(g θ-c)^2 :=
    intervalIntegral.integral_nonneg_of_forall hb.le (fun θ=>sq_nonneg _)
  have he : (∫ θ in (0:ℝ)..b,(g θ-c)^2)=J-2*c*I+b*c^2 := by
    have hfun : (fun θ=>(g θ-c)^2)=(fun θ=>(g θ)^2-(2*c)*g θ+c^2) := by funext θ;ring
    have h0 : Continuous (fun θ:ℝ=>(g θ)^2) := hg.pow 2
    have h1 : Continuous (fun θ:ℝ=>(g θ)^2-(2*c)*g θ) := h0.sub (continuous_const.mul hg)
    have h2 : Continuous (fun _:ℝ=>c^2) := continuous_const
    have h3 : Continuous (fun θ:ℝ=>(2*c)*g θ) := continuous_const.mul hg
    rw [hfun,intervalIntegral.integral_add (h1.intervalIntegrable 0 b) (h2.intervalIntegrable 0 b),
      intervalIntegral.integral_sub (h0.intervalIntegrable 0 b) (h3.intervalIntegrable 0 b),
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const]
    simp only [sub_zero,smul_eq_mul,I,J]
  rw [he] at hpos
  have hc : b*c=I := by dsimp [c];field_simp
  have hmul := mul_nonneg hb.le hpos
  have he' : b*(J-2*c*I+b*c^2)=b*J-I^2 := by
    calc
      _ = b*J-2*(b*c)*I+(b*c)^2 := by ring
      _ = _ := by rw [hc];ring
  rw [he'] at hmul
  exact sub_nonneg.mp hmul
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem c1_rotation_square (f : E→ℝ) (hf : ContDiff ℝ 1 f) (z : E×E) :
    (f z.2-f z.1)^2≤(Real.pi/2)*(∫ θ in (0:ℝ)..Real.pi/2,
      ((fderiv ℝ f (ContinuousLinearMap.rotation θ z).1)
        (ContinuousLinearMap.rotation θ z).2)^2) := by
  have hc : Continuous (fun θ:ℝ=>(fderiv ℝ f (ContinuousLinearMap.rotation θ z).1)
      (ContinuousLinearMap.rotation θ z).2) := by
    apply (hf.continuous_fderiv_apply (by norm_num)).comp
    simp only [ContinuousLinearMap.rotation_apply]
    fun_prop
  simpa only [Qatlib.Foundations.ProbabilityCore.GaussPoincare.Directional.rotation_path_integral f hf z] using
    angle_square_cauchy _ hc (Real.pi/2) (by positivity)
end Qatlib.Foundations.ProbabilityCore.GaussPoincare.AngleIntegral
