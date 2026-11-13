/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianCore

/-!
# Symmetries of the Gaussian correlation kernel

Negating the Gaussian noise coordinate preserves `sourceLaw` and proves that `actualKernel` is
odd. The pushforward `roundedLaw` packages the normalized pair, whose expected inner product has
the kernel values zero, one, and minus one at the corresponding correlation parameters. See
[CrostaSaubanereHuber2026].

## Main statements

* `actualKernel_odd`: proves oddness of the normalized Gaussian kernel.
* `roundedLaw_expect`: identifies the rounded-pair expectation with `actualKernel`.
* `roundedLaw_three_values`: records the zero and endpoint expectations.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianPair

/-- Negation preserves the standard three-dimensional Gaussian measure. -/
theorem gamma_neg_preserving : MeasurePreserving (fun x : V => -x) gamma gamma := by
  refine ⟨by fun_prop,?_⟩
  exact stdGaussian_map (LinearIsometryEquiv.neg ℝ : V ≃ₗᵢ[ℝ] V)

/-- The map that keeps the first source vector and negates the second. -/
def reflectNoise (w : V × V) : V × V := (w.1,-w.2)

/-- Negating the noise vector preserves the independent Gaussian source law. -/
theorem reflectNoise_preserving : MeasurePreserving reflectNoise sourceLaw sourceLaw :=
  (MeasurePreserving.id gamma).prod gamma_neg_preserving

/-- Negating the correlation parameter and reflecting the noise negates the normalized pair
correlation. -/
theorem pairCorrelation_neg_reflect (t : ℝ) (w : V × V) :
    pairCorrelation (-t) (reflectNoise w)= -pairCorrelation t w := by
  have hy : correlated (-t) (reflectNoise w)= -correlated t w := by
    simp [correlated,reflectNoise,neg_smul,smul_neg,add_comm]
  change inner ℝ (unitVector w.1)
      (unitVector (correlated (-t) (reflectNoise w)))= -pairCorrelation t w
  rw [hy,unitVector_neg,inner_neg_right]
  rfl

/-- The normalized Gaussian correlation kernel is odd. -/
theorem actualKernel_odd (t : ℝ) : actualKernel (-t)= -actualKernel t := by
  have h := integral_map (μ:=sourceLaw) reflectNoise_preserving.measurable.aemeasurable
    (pairCorrelation_measurable (-t)).aestronglyMeasurable
  rw [reflectNoise_preserving.map_eq] at h
  have he : (fun w => pairCorrelation (-t) (reflectNoise w))=fun w => -pairCorrelation t w :=
    funext (pairCorrelation_neg_reflect t)
  rw [he,integral_neg] at h
  exact h

/-- The normalized Gaussian correlation kernel vanishes at zero. -/
theorem actualKernel_zero : actualKernel 0=0 := by
  have h := actualKernel_odd 0
  rw [neg_zero] at h
  linarith

/-- The pair consisting of the normalized first source vector and the normalized correlated
vector. -/
def roundedPair (t : ℝ) (w : V × V) : V × V := (unitVector w.1,unitVector (correlated t w))

/-- The normalized pair map is measurable for every real correlation parameter. -/
theorem roundedPair_measurable (t : ℝ) : Measurable (roundedPair t) := by
  have hy : Measurable (correlated t) := by unfold correlated; fun_prop
  exact (unitVector_measurable.comp measurable_fst).prodMk (unitVector_measurable.comp hy)

/-- The pushforward of the Gaussian source law by the normalized pair map. -/
def roundedLaw (t : ℝ) : Measure (V × V) := sourceLaw.map (roundedPair t)

instance roundedLaw_probability (t : ℝ) : IsProbabilityMeasure (roundedLaw t) :=
  by unfold roundedLaw; infer_instance

/-- The expected inner product under the rounded-pair law equals `actualKernel`. -/
theorem roundedLaw_expect (t : ℝ) :
    (∫ p : V × V,inner ℝ p.1 p.2 ∂roundedLaw t)=actualKernel t := by
  exact integral_map (roundedPair_measurable t).aemeasurable (by fun_prop)

/-- The expected inner products under `roundedLaw 0`, `roundedLaw 1`, and `roundedLaw (-1)` are
respectively zero, one, and minus one. -/
theorem roundedLaw_three_values :
    (∫ p : V × V,inner ℝ p.1 p.2 ∂roundedLaw 0)=0 ∧
    (∫ p : V × V,inner ℝ p.1 p.2 ∂roundedLaw 1)=1 ∧
    (∫ p : V × V,inner ℝ p.1 p.2 ∂roundedLaw (-1))= -1 := by
  simp only [roundedLaw_expect,actualKernel_zero,actualKernel_one,actualKernel_neg_one,and_self]

end Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianPair
