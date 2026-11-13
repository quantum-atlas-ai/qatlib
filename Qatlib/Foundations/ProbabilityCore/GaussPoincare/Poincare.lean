/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.ProbabilityCore.GaussPoincare.AngleIntegral

/-!
# A Gaussian Poincare estimate from pair rotations

For C¹ functions on a finite-dimensional real inner product space, this module derives a
Gaussian Poincare bound with constant π²/8. The proof relates independent-pair increments to
variance and integrates squared directional derivatives along Gaussian-preserving rotations, an
interpolation method relevant to [GohMuller2026].

## Main statements

* `pair_increment_square_memLp`: The squared increment between independent Gaussian inputs has
  mean twice the variance.
* `rotated_gradient_square`: Rotated directional energy equals the Gaussian squared-derivative
  integral.
* `c1_gaussian_poincare_gradient`: Variance is bounded by π²/8 times the squared-derivative
  integral.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical NNReal
namespace Qatlib.Foundations.ProbabilityCore.GaussPoincare.Poincare
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- For a Gaussian square-integrable function, the integral of its squared increment between two
independent standard Gaussian inputs is twice its variance. -/
theorem pair_increment_square_memLp (f : E→ℝ) (hm : MemLp f 2 (stdGaussian E)) :
    (∫ z:E×E,(f z.2-f z.1)^2 ∂((stdGaussian E).prod (stdGaussian E))) =
      2*variance f (stdGaussian E) := by
  have hd := (hm.comp_snd (stdGaussian E)).sub (hm.comp_fst (stdGaussian E))
  have hmean : (∫ z:E×E,f z.2-f z.1 ∂((stdGaussian E).prod (stdGaussian E)))=0 := by
    rw [integral_sub ((hm.integrable (by norm_num)).comp_snd (stdGaussian E))
      ((hm.integrable (by norm_num)).comp_fst (stdGaussian E)),integral_fun_snd,integral_fun_fst]
    simp
  have hv : variance (fun z:E×E=>f z.2-f z.1) ((stdGaussian E).prod (stdGaussian E)) =
      2*variance f (stdGaussian E) := by
    have h := variance_add_prod hm.neg hm
    simpa only [Pi.neg_apply,neg_add_eq_sub,variance_neg,two_mul] using h
  have h := variance_eq_sub hd
  simp only [Pi.sub_apply,Pi.pow_apply] at h
  rw [hmean,zero_pow (by norm_num : (2:ℕ)≠0),sub_zero] at h
  exact h.symm.trans hv

/-- If a C¹ function has integrable squared derivative norm, its squared derivative evaluated on
an independent Gaussian direction is integrable under the Gaussian product measure. -/
theorem gradient_pair_integrable (f : E→ℝ) (hf : ContDiff ℝ 1 f)
    (hgrad : Integrable (fun x:E=>‖fderiv ℝ f x‖^2) (stdGaussian E)) :
    Integrable (fun z:E×E=>((fderiv ℝ f z.1) z.2)^2)
      ((stdGaussian E).prod (stdGaussian E)) := by
  have hc : Continuous (fun z:E×E=>((fderiv ℝ f z.1) z.2)^2) :=
      (hf.continuous_fderiv_apply (by norm_num)).pow 2
  apply (integrable_prod_iff hc.aestronglyMeasurable).mpr
  constructor
  · apply Filter.Eventually.of_forall
    intro x
    have hl : MemLp (fderiv ℝ f x) 2 (stdGaussian E) :=
      (fderiv ℝ f x).lipschitz.comp_memLp (map_zero _) (IsGaussian.memLp_id (stdGaussian E) 2 (by simp))
    simpa only [Real.norm_eq_abs,sq_abs] using! hl.integrable_norm_pow'
  · simpa only
      [Real.norm_eq_abs,abs_pow,sq_abs,Qatlib.Foundations.ProbabilityCore.GaussPoincare.Directional.dual_square_integral] using! hgrad

/-- For a C¹ function with integrable squared derivative norm, the rotated squared directional
derivative is jointly integrable over angles in (0, π/2] and the Gaussian pair. -/
theorem angle_gradient_integrable (f : E→ℝ) (hf : ContDiff ℝ 1 f)
    (hgrad : Integrable (fun x:E=>‖fderiv ℝ f x‖^2) (stdGaussian E)) :
    Integrable (fun p:ℝ×(E×E)=>
      ((fderiv ℝ f (ContinuousLinearMap.rotation p.1 p.2).1)
        (ContinuousLinearMap.rotation p.1 p.2).2)^2)
      ((volume.restrict (Set.Ioc (0:ℝ) (Real.pi/2))).prod
        ((stdGaussian E).prod (stdGaussian E))) := by
  let μ := (stdGaussian E).prod (stdGaussian E)
  let ν := volume.restrict (Set.Ioc (0:ℝ) (Real.pi/2))
  let k := fun z:E×E=>((fderiv ℝ f z.1) z.2)^2
  have hk : Integrable k μ := gradient_pair_integrable f hf hgrad
  have hc : Continuous (fun p:ℝ×(E×E)=>
      (fderiv ℝ f (ContinuousLinearMap.rotation p.1 p.2).1)
        (ContinuousLinearMap.rotation p.1 p.2).2) := by
    apply (hf.continuous_fderiv_apply (by norm_num)).comp
    simp only [ContinuousLinearMap.rotation_apply]
    fun_prop
  apply (integrable_prod_iff (hc.pow 2).aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall fun θ=>(Qatlib.Foundations.ProbabilityCore.GaussPoincare.Rotation.rotation_preserving θ).integrable_comp_of_integrable hk
  · have he (θ:ℝ) : (∫ z:E×E,‖k (ContinuousLinearMap.rotation θ z)‖ ∂μ)=∫ z:E×E,‖k z‖ ∂μ :=
      Qatlib.Foundations.ProbabilityCore.GaussPoincare.Rotation.rotation_integral θ (fun z=>‖k z‖) hk.norm.aestronglyMeasurable
    have hh : (fun θ:ℝ=>∫ z:E×E,‖k (ContinuousLinearMap.rotation θ z)‖ ∂μ)=
        fun _ : ℝ=>∫ z:E×E,‖k z‖ ∂μ := funext he
    change Integrable (fun θ:ℝ=>∫ z:E×E,‖k (ContinuousLinearMap.rotation θ z)‖ ∂μ) ν
    rw [hh]
    exact integrable_const _

/-- For a C¹ function with integrable squared derivative norm, the Gaussian integral of the
rotated squared directional derivative equals the integral of the squared derivative norm. -/
theorem rotated_gradient_square (f : E→ℝ) (hf : ContDiff ℝ 1 f)
    (hgrad : Integrable (fun x:E=>‖fderiv ℝ f x‖^2) (stdGaussian E)) (θ : ℝ) :
    (∫ z:E×E,((fderiv ℝ f (ContinuousLinearMap.rotation θ z).1)
      (ContinuousLinearMap.rotation θ z).2)^2 ∂((stdGaussian E).prod (stdGaussian E))) =
      ∫ x,‖fderiv ℝ f x‖^2 ∂stdGaussian E := by
  have hk := gradient_pair_integrable f hf hgrad
  rw [Qatlib.Foundations.ProbabilityCore.GaussPoincare.Rotation.rotation_integral θ (fun z:E×E=>((fderiv ℝ f z.1) z.2)^2)
    hk.aestronglyMeasurable,integral_prod _ hk]
  exact integral_congr_ae
      (Filter.Eventually.of_forall fun x=>Qatlib.Foundations.ProbabilityCore.GaussPoincare.Directional.dual_square_integral (fderiv ℝ f x))

/-- A C¹ Gaussian square-integrable function with integrable squared derivative norm has
variance at most π²/8 times the Gaussian integral of that squared norm. -/
theorem c1_gaussian_poincare_gradient (f : E→ℝ) (hf : ContDiff ℝ 1 f)
    (hm : MemLp f 2 (stdGaussian E))
    (hgrad : Integrable (fun x:E=>‖fderiv ℝ f x‖^2) (stdGaussian E)) :
    variance f (stdGaussian E)≤(Real.pi^2/8)*(∫ x,‖fderiv ℝ f x‖^2 ∂stdGaussian E) := by
  let μ := (stdGaussian E).prod (stdGaussian E)
  let ν := volume.restrict (Set.Ioc (0:ℝ) (Real.pi/2))
  let g := fun θ:ℝ=>fun z:E×E=>
    ((fderiv ℝ f (ContinuousLinearMap.rotation θ z).1)
      (ContinuousLinearMap.rotation θ z).2)^2
  have hg : Integrable (Function.uncurry g) (ν.prod μ) := angle_gradient_integrable f hf hgrad
  have hpos : 0<Real.pi/2 := by positivity
  have ht : (∫ z, (∫ θ in (0:ℝ)..Real.pi/2,g θ z) ∂μ) =
      (Real.pi/2)*(∫ x,‖fderiv ℝ f x‖^2 ∂stdGaussian E) := by
    simp only [intervalIntegral.integral_of_le hpos.le]
    rw [← integral_integral_swap hg]
    simp_rw [show ∀ θ:ℝ,(∫ z:E×E,g θ z ∂μ)=∫ x,‖fderiv ℝ f x‖^2 ∂stdGaussian E
      from fun θ=>rotated_gradient_square f hf hgrad θ]
    change (∫ θ in Set.Ioc (0:ℝ) (Real.pi/2),(∫ x,‖fderiv ℝ f x‖^2 ∂stdGaussian E))=_
    rw [← intervalIntegral.integral_of_le hpos.le,intervalIntegral.integral_const]
    simp only [sub_zero,smul_eq_mul]
  have hd := (hm.comp_snd (stdGaussian E)).sub (hm.comp_fst (stdGaussian E))
  have hdi : Integrable (fun z:E×E=>(f z.2-f z.1)^2) μ := by
    simpa only [Real.norm_eq_abs,sq_abs] using! hd.integrable_norm_pow'
  have hgi : Integrable (fun z:E×E=> (Real.pi/2)*(∫ θ in (0:ℝ)..Real.pi/2,g θ z)) μ := by
    simp only [intervalIntegral.integral_of_le hpos.le]
    exact hg.integral_prod_right.const_mul _
  have h := integral_mono_ae hdi hgi
    (Filter.Eventually.of_forall fun z=>Qatlib.Foundations.ProbabilityCore.GaussPoincare.AngleIntegral.c1_rotation_square f hf z)
  rw [integral_const_mul,pair_increment_square_memLp f hm,ht] at h
  nlinarith
end Qatlib.Foundations.ProbabilityCore.GaussPoincare.Poincare
