/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# Gaussian source and normalized correlation kernel

The Gaussian source `sourceLaw` consists of two independent standard Gaussian vectors in three
dimensions. The module defines zero-safe normalization, correlated vector pairs, and their
expected normalized inner product `actualKernel`, with measurability, integrability, bounds, and
endpoint values. See [CrostaSaubanereHuber2026].

## Main statements

* `actualKernel_bound`: bounds the absolute kernel value by one.
* `actualKernel_one`: evaluates the kernel at correlation one.
* `actualKernel_neg_one`: evaluates the kernel at correlation minus one.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory

namespace Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianPair

/-- Three-dimensional real Euclidean space for Gaussian projections. -/
abbrev V := EuclideanSpace ℝ (Fin 3)

/-- The standard Gaussian measure on three-dimensional real Euclidean space. -/
abbrev gamma : Measure V := stdGaussian V

/-- The product law of two independent standard Gaussian vectors. -/
abbrev sourceLaw : Measure (V × V) := gamma.prod gamma

/-- Converting three independent standard real Gaussians to a Euclidean vector yields the
standard Gaussian measure `gamma`. -/
theorem gamma_from_iid :
    (Measure.pi (fun _ : Fin 3 => gaussianReal 0 1)).map (WithLp.toLp 2)=gamma :=
  map_pi_eq_stdGaussian

/-- The vector `‖x‖⁻¹ • x`, with value zero at the zero vector. -/
def unitVector (x : V) : V := ‖x‖⁻¹ • x

/-- Normalization maps the zero vector to zero. -/
theorem unitVector_zero : unitVector 0=0 := by simp [unitVector]

/-- The normalization of a nonzero vector has norm one. -/
theorem norm_unitVector (x : V) (hx : x≠0) : ‖unitVector x‖=1 := by
  rw [unitVector,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

/-- The norm of a normalized vector is at most one, including at zero. -/
theorem norm_unitVector_le (x : V) : ‖unitVector x‖≤1 := by
  by_cases h : x=0
  · simp [h,unitVector_zero]
  · rw [norm_unitVector x h]

/-- Normalization commutes with negation. -/
theorem unitVector_neg (x : V) : unitVector (-x)= -unitVector x := by
  simp only [unitVector,norm_neg,smul_neg]

/-- The vector normalization map is measurable. -/
theorem unitVector_measurable : Measurable unitVector :=
  measurable_id.norm.inv.smul measurable_id

/-- The absolute inner product of two normalized vectors is at most one. -/
theorem unit_inner_bound (x y : V) : |inner ℝ (unitVector x) (unitVector y)|≤1 := by
  calc
    _ ≤ ‖unitVector x‖*‖unitVector y‖ := abs_real_inner_le_norm _ _
    _ ≤ 1*1 := mul_le_mul (norm_unitVector_le x) (norm_unitVector_le y) (norm_nonneg _) (by norm_num)
    _ = 1 := by ring

/-- The correlated vector `t • w.1 + √(1 - t²) • w.2`. -/
def correlated (t : ℝ) (w : V × V) : V := t • w.1+Real.sqrt (1-t^2) • w.2

/-- The continuous linear map sending a pair to its first vector and the corresponding
correlated vector. -/
def pairLinear (t : ℝ) : (V × V) →L[ℝ] (V × V) :=
  (ContinuousLinearMap.fst ℝ V V).prod
    (t • ContinuousLinearMap.fst ℝ V V+Real.sqrt (1-t^2) • ContinuousLinearMap.snd ℝ V V)

/-- The pushforward of the independent Gaussian source law by `pairLinear t`. -/
def correlatedLaw (t : ℝ) : Measure (V × V) := sourceLaw.map (pairLinear t)

/-- The correlated pair law is Gaussian for every real parameter `t`. -/
theorem correlatedLaw_isGaussian (t : ℝ) : IsGaussian (correlatedLaw t) := by
  exact isGaussian_map_of_measurable (L:=pairLinear t) (by fun_prop)

instance correlatedLaw_probability (t : ℝ) : IsProbabilityMeasure (correlatedLaw t) :=
  by unfold correlatedLaw; infer_instance

/-- The inner product of the normalized first vector and the normalized correlated vector. -/
def pairCorrelation (t : ℝ) (w : V × V) : ℝ :=
    inner ℝ (unitVector w.1) (unitVector (correlated t w))

/-- The normalized pair correlation is measurable for every real parameter. -/
theorem pairCorrelation_measurable (t : ℝ) : Measurable (pairCorrelation t) := by
  have hY : Measurable (correlated t) := by unfold correlated; fun_prop
  exact (unitVector_measurable.comp measurable_fst).inner (unitVector_measurable.comp hY)

/-- The normalized pair correlation is integrable under the Gaussian source law. -/
theorem pairCorrelation_integrable (t : ℝ) : Integrable (pairCorrelation t) sourceLaw := by
  exact (integrable_const (1:ℝ)).mono' (pairCorrelation_measurable t).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun w => unit_inner_bound w.1 (correlated t w)))

/-- The expected normalized pair correlation under the independent Gaussian source law. -/
def actualKernel (t : ℝ) : ℝ := ∫ w,pairCorrelation t w ∂sourceLaw

/-- The absolute value of the Gaussian rounding kernel is at most one. -/
theorem actualKernel_bound (t : ℝ) : |actualKernel t|≤1 := by
  apply (abs_integral_le_integral_abs).trans
  calc
    (∫ w,|pairCorrelation t w| ∂sourceLaw) ≤ ∫ _w,(1:ℝ) ∂sourceLaw :=
      integral_mono_ae (pairCorrelation_integrable t).abs (integrable_const _)
        (Filter.Eventually.of_forall (fun w => unit_inner_bound w.1 (correlated t w)))
    _ = 1 := by simp

/-- Every coordinate of the standard three-dimensional Gaussian vector has the standard real
Gaussian law. -/
theorem gamma_coordinate (i : Fin 3) :
    MeasurePreserving (fun x : V => x i) gamma (gaussianReal 0 1) := by
  simpa using
      (measurePreserving_eval_multivariateGaussian (μ:=(0:V)) (S:=(1:Matrix (Fin 3) (Fin 3) ℝ)) Matrix.PosSemidef.one (i:=i))

/-- A standard Gaussian vector differs from any prescribed vector almost surely. -/
theorem gamma_ae_ne (a : V) : ∀ᵐ x ∂gamma,x≠a := by
  letI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have h : ∀ᵐ r ∂(gaussianReal 0 1),r≠a 0 := (gaussianReal 0 1).ae_ne (a 0)
  filter_upwards [(gamma_coordinate 0).quasiMeasurePreserving.ae h] with x hx
  intro he
  exact hx (by rw [he])

/-- The first vector in the Gaussian source pair is nonzero almost surely. -/
theorem source_first_ne_zero : ∀ᵐ w ∂sourceLaw,w.1≠0 :=
  (measurePreserving_fst (μ:=gamma) (ν:=gamma)).quasiMeasurePreserving.ae (gamma_ae_ne 0)

/-- The normalized Gaussian correlation kernel has value one at correlation one. -/
theorem actualKernel_one : actualKernel 1=1 := by
  have h : pairCorrelation 1 =ᵐ[sourceLaw] (fun _ => (1:ℝ)) := by
    filter_upwards [source_first_ne_zero] with w hw
    simp only [pairCorrelation,correlated,one_pow,sub_self,Real.sqrt_zero,zero_smul,add_zero,one_smul,
      real_inner_self_eq_norm_sq,norm_unitVector w.1 hw,one_pow]
  rw [actualKernel,integral_congr_ae h]
  simp

/-- The normalized Gaussian correlation kernel has value minus one at correlation minus one. -/
theorem actualKernel_neg_one : actualKernel (-1)= -1 := by
  have h : pairCorrelation (-1) =ᵐ[sourceLaw] (fun _ => (-1:ℝ)) := by
    filter_upwards [source_first_ne_zero] with w hw
    norm_num only [pairCorrelation,correlated,neg_one_sq,sub_self,Real.sqrt_zero,zero_smul,add_zero,neg_one_smul,
      unitVector_neg,inner_neg_right,real_inner_self_eq_norm_sq,norm_unitVector w.1 hw,one_pow]
  rw [actualKernel,integral_congr_ae h]
  simp

end Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianPair
