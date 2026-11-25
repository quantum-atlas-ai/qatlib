/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.OrientedGaussLimit

/-!
# Weak Gauss limits for finite oriented measures

The probability normalization is only used to prove continuity of
the regularized product integral. Restoring the two mass factors
recovers the kernel, integrability, and close-pair bounds for the
original finite oriented measures.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfluidHel18.CenterlineCL

open Filter MeasureTheory Set
open scoped ENNReal Topology

/-- The product of a finite measure with itself is the product
of its probability normalization multiplied by the square of its mass. -/
private theorem finiteSelfProd_eq_normalize (ν : FiniteMeasure VorticityElement) :
    ν.toMeasure.prod ν.toMeasure =
      (ν.mass : ℝ≥0∞) ^ 2 • (ν.normalize.prod ν.normalize).toMeasure := by
  rw [finiteMeasure_eq_mass_smul_normalize ν, Measure.prod_smul_left, Measure.prod_smul_right,
    smul_smul, pow_two, ProbabilityMeasure.toMeasure_prod]

/-- For a nonzero finite measure, normalization preserves absolute
integrability of test functions on the self product. -/
private theorem integrable_normalizedSelfProd {ν : FiniteMeasure VorticityElement}
    (hν : ν ≠ 0) {f : VorticityElement × VorticityElement → ℝ}
    (hf : Integrable f (ν.toMeasure.prod ν.toMeasure)) :
    Integrable f (ν.normalize.prod ν.normalize).toMeasure := by
  have h₀ : (ν.mass : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast ν.mass_nonzero_iff.mpr hν
  rw [finiteSelfProd_eq_normalize] at hf
  exact (integrable_smul_measure (pow_ne_zero 2 h₀) (by simp)).mp hf

/-- Restriction of the self product preserves the same squared mass
relation, so the near-pair bound can be checked before normalization. -/
private theorem setIntegral_finiteSelfProd (ν : FiniteMeasure VorticityElement)
    (s : Set (VorticityElement × VorticityElement)) (f : VorticityElement × VorticityElement → ℝ) :
    (∫ p in s, f p ∂(ν.toMeasure.prod ν.toMeasure)) =
      (ν.mass : ℝ) ^ 2 * ∫ p in s, f p ∂(ν.normalize.prod ν.normalize).toMeasure := by
  rw [finiteSelfProd_eq_normalize, Measure.restrict_smul, integral_smul_measure]
  simp only [ENNReal.toReal_pow, ENNReal.coe_toReal, smul_eq_mul]

/-- A weakly converging family of finite nonzero oriented measures
has convergent full Gauss self-pairings when the absolute interaction
of spatially close pairs is uniformly small. -/
theorem tendsto_finiteGaussPairing {ι : Type*} {l : Filter ι}
    {F : ι → FiniteMeasure VorticityElement} {μ : FiniteMeasure VorticityElement}
    (hF : Tendsto F l (𝓝 μ)) (hne : ∀ i, F i ≠ 0) (hμne : μ ≠ 0)
    (hfull : ∀ i, Integrable (fun p => gaussSoftKernel 0 p.1 p.2)
      ((F i).toMeasure.prod (F i).toMeasure))
    (hμ : Integrable (fun p => gaussSoftKernel 0 p.1 p.2) (μ.toMeasure.prod μ.toMeasure))
    (hnear : ∀ ε > 0, ∀ b > 0, ∃ δ ∈ Ioo 0 b, ∀ᶠ i in l,
      (∫ p in gaussNearPairs δ, |gaussSoftKernel 0 p.1 p.2|
          ∂((F i).toMeasure.prod (F i).toMeasure)) < ε) :
    Tendsto (fun i => ∫ p, gaussSoftKernel 0 p.1 p.2 ∂((F i).toMeasure.prod (F i).toMeasure)) l
      (𝓝 (∫ p, gaussSoftKernel 0 p.1 p.2 ∂(μ.toMeasure.prod μ.toMeasure))) := by
  have hn := FiniteMeasure.tendsto_normalize_of_tendsto hF hμne
  have hm : Tendsto (fun i => ((F i).mass : ℝ)) l (𝓝 (μ.mass : ℝ)) :=
    (NNReal.continuous_coe.comp FiniteMeasure.continuous_mass).continuousAt.tendsto.comp hF
  have hnear' (ε : ℝ) (hε : 0 < ε) (b : ℝ) (hb : 0 < b) :
      ∃ δ ∈ Ioo 0 b, ∀ᶠ i in l, ((F i).mass : ℝ) ^ 2 *
        (∫ p in gaussNearPairs δ, |gaussSoftKernel 0 p.1 p.2|
          ∂((F i).normalize.prod (F i).normalize).toMeasure) < ε := by
    obtain ⟨δ, hδ, he⟩ := hnear ε hε b hb
    refine ⟨δ, hδ, he.mono fun i hi => ?_⟩
    rwa [← setIntegral_finiteSelfProd]
  simpa only [orientedGaussSelf_mass_normalize] using
    tendsto_orientedGaussSelf hn hm (fun i => integrable_normalizedSelfProd (hne i) (hfull i))
      (integrable_normalizedSelfProd hμne hμ) hnear'

end Qatlib.Papers.SuperfluidHel18.CenterlineCL
