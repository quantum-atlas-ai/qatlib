/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.CosineFiniteCircle
import Qatlib.Foundations.CbmdAnalysis.Core.AiryMixture
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
noncomputable section
namespace CBMD
open Complex
open scoped BigOperators Topology

section BanachAlgebra
variable {E : Type*} [NormedRing E] [NormedAlgebra ℂ E] [CompleteSpace E]

def waveCosineNumerator (L H : E) (t : ℂ) (z : ℂ) : E :=
  wavePropagator (L + (I * z) • H) t

def besselCosineNumerator (L H : E) (t : ℂ) (z : ℂ) : E :=
  besselPropagator (L + (I * z) • H) t

def airyCosineNumerator (L H : E) (t : ℂ) (z : ℂ) : E :=
  airyPropagator (L + (I * z) • H) t

theorem waveCosineNumerator_differentiable (L H : E) (t : ℂ) :
    Differentiable ℂ (waveCosineNumerator L H t) := by
  intro z
  change DifferentiableAt ℂ (fun w => wavePropagator (L + (I * w) • H) t) z
  have h := wave_series_affine_analytic L (I • H) t z
  simpa only [wavePropagator, smul_smul, mul_comm] using! h.differentiableAt

theorem besselCosineNumerator_differentiable (L H : E) (t : ℂ) :
    Differentiable ℂ (besselCosineNumerator L H t) := by
  intro z
  change DifferentiableAt ℂ (fun w => besselPropagator (L + (I * w) • H) t) z
  have h := bessel_series_affine_analytic L (I • H) t z
  simpa only [besselPropagator, smul_smul, mul_comm] using! h.differentiableAt

theorem airyCosineNumerator_differentiable (L H : E) (t : ℂ) :
    Differentiable ℂ (airyCosineNumerator L H t) := by
  intro z
  change DifferentiableAt ℂ (fun w => airyPropagator (L + (I * w) • H) t) z
  have h := airy_series_affine_analytic L (I • H) t z
  simpa only [airyPropagator, smul_smul, mul_comm] using! h.differentiableAt

omit [CompleteSpace E] in

theorem cosinePencil_target (L H : E) : L + (I * (1 : ℂ)) • H = L + I • H := by simp

omit [CompleteSpace E] in

theorem cosinePencil_sample (L H : E) (γ τ : ℝ) (k : ℕ) :
    L + (I * cosineSamplePole γ τ k) • H =
      L + (cosineSampleScale γ τ k : ℂ) • H := by
  simp [cosineSamplePole, ← mul_assoc]

omit [CompleteSpace E] in

theorem waveCosineNumerator_sample (L H : E) (t : ℂ) (γ τ : ℝ) (k : ℕ) :
    waveCosineNumerator L H t (cosineSamplePole γ τ k) =
      wavePropagator (L + (cosineSampleScale γ τ k : ℂ) • H) t := by
  rw [waveCosineNumerator, cosinePencil_sample]

omit [CompleteSpace E] in

theorem besselCosineNumerator_sample (L H : E) (t : ℂ) (γ τ : ℝ) (k : ℕ) :
    besselCosineNumerator L H t (cosineSamplePole γ τ k) =
      besselPropagator (L + (cosineSampleScale γ τ k : ℂ) • H) t := by
  rw [besselCosineNumerator, cosinePencil_sample]

omit [CompleteSpace E] in

theorem airyCosineNumerator_sample (L H : E) (t : ℂ) (γ τ : ℝ) (k : ℕ) :
    airyCosineNumerator L H t (cosineSamplePole γ τ k) =
      airyPropagator (L + (cosineSampleScale γ τ k : ℂ) • H) t := by
  rw [airyCosineNumerator, cosinePencil_sample]

theorem wave_cosine_circle_identity (L H : E) {γ t : ℝ}
    (hγ : 0 < γ) (ht : 0 < t) (N : ℕ) (hR : 1 < cosineCircleRadius γ t N) :
    (2 * (Real.pi : ℂ) * I)⁻¹ •
      (∮ z in C(0, cosineCircleRadius γ t N),
        cosineContourIntegrand γ t (waveCosineNumerator L H (t : ℂ)) z) =
      wavePropagator (L + I • H) (t : ℂ) -
        cosineRegulator γ t 1 • wavePropagator L (t : ℂ) +
        cosineRegulator γ t 1 • ∑ k ∈ Finset.range N,
          cosineSampleCoefficient γ t k •
            wavePropagator (L + (cosineSampleScale γ t k : ℂ) • H) (t : ℂ) := by
  have h := cosineContour_circle_identity_normalized hγ ht N hR
    (waveCosineNumerator L H (t : ℂ)) (waveCosineNumerator_differentiable L H (t : ℂ))
  simpa only [cosineLCUSum, cosineSample, waveCosineNumerator, cosinePencil_sample,
    mul_one, mul_zero, zero_smul, add_zero] using! h

theorem bessel_cosine_circle_identity (L H : E) {γ t : ℝ}
    (hγ : 0 < γ) (ht : 0 < t) (N : ℕ) (hR : 1 < cosineCircleRadius γ t N) :
    (2 * (Real.pi : ℂ) * I)⁻¹ •
      (∮ z in C(0, cosineCircleRadius γ t N),
        cosineContourIntegrand γ t (besselCosineNumerator L H (t : ℂ)) z) =
      besselPropagator (L + I • H) (t : ℂ) -
        cosineRegulator γ t 1 • besselPropagator L (t : ℂ) +
        cosineRegulator γ t 1 • ∑ k ∈ Finset.range N,
          cosineSampleCoefficient γ t k •
            besselPropagator (L + (cosineSampleScale γ t k : ℂ) • H) (t : ℂ) := by
  have h := cosineContour_circle_identity_normalized hγ ht N hR
    (besselCosineNumerator L H (t : ℂ)) (besselCosineNumerator_differentiable L H (t : ℂ))
  simpa only [cosineLCUSum, cosineSample, besselCosineNumerator, cosinePencil_sample,
    mul_one, mul_zero, zero_smul, add_zero] using! h

theorem airy_cosine_circle_identity (L H : E) {γ t : ℝ}
    (hγ : 0 < γ) (ht : 0 < t) (N : ℕ)
    (hR : 1 < cosineCircleRadius γ (airyTimeScale t) N) :
    (2 * (Real.pi : ℂ) * I)⁻¹ •
      (∮ z in C(0, cosineCircleRadius γ (airyTimeScale t) N),
        cosineContourIntegrand γ (airyTimeScale t) (airyCosineNumerator L H (t : ℂ)) z) =
      airyPropagator (L + I • H) (t : ℂ) -
        cosineRegulator γ (airyTimeScale t) 1 • airyPropagator L (t : ℂ) +
        cosineRegulator γ (airyTimeScale t) 1 • ∑ k ∈ Finset.range N,
          cosineSampleCoefficient γ (airyTimeScale t) k •
            airyPropagator (L + (cosineSampleScale γ (airyTimeScale t) k : ℂ) • H) (t : ℂ) := by
  have hs : 0 < airyTimeScale t := by unfold airyTimeScale; positivity
  have h := cosineContour_circle_identity_normalized hγ hs N hR
    (airyCosineNumerator L H (t : ℂ)) (airyCosineNumerator_differentiable L H (t : ℂ))
  simpa only [cosineLCUSum, cosineSample, airyCosineNumerator, cosinePencil_sample,
    mul_one, mul_zero, zero_smul, add_zero] using! h

end BanachAlgebra

section Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in

theorem cosineSampleMatrix_posSemidef (L H : Matrix n n ℂ)
    (hL : L.PosSemidef) (hH : H.PosSemidef) {γ τ : ℝ}
    (hγ : 0 < γ) (hτ : 0 < τ) (k : ℕ) :
    (L + (cosineSampleScale γ τ k : ℂ) • H).PosSemidef := by
  exact hL.add (hH.smul (show (0 : ℂ) ≤ (cosineSampleScale γ τ k : ℂ) by
    exact_mod_cast (cosineSampleScale_pos hγ hτ k).le))

theorem waveCosineNumerator_sample_norm_le_one (L H : Matrix n n ℂ)
    (hL : L.PosSemidef) (hH : H.PosSemidef) {γ τ : ℝ}
    (hγ : 0 < γ) (hτ : 0 < τ) (t : ℝ) (k : ℕ) :
    ‖waveCosineNumerator L H (t : ℂ) (cosineSamplePole γ τ k)‖ ≤ 1 := by
  rw [waveCosineNumerator_sample]
  exact wavePropagator_posSemidef_norm_le_one _
    (cosineSampleMatrix_posSemidef L H hL hH hγ hτ k) t

theorem besselCosineNumerator_sample_norm_le_one (L H : Matrix n n ℂ)
    (hL : L.PosSemidef) (hH : H.PosSemidef) {γ τ : ℝ}
    (hγ : 0 < γ) (hτ : 0 < τ) (t : ℝ) (k : ℕ) :
    ‖besselCosineNumerator L H (t : ℂ) (cosineSamplePole γ τ k)‖ ≤ 1 := by
  rw [besselCosineNumerator_sample]
  exact besselPropagator_posSemidef_norm_le_one _
    (cosineSampleMatrix_posSemidef L H hL hH hγ hτ k) t

theorem airyCosineNumerator_sample_norm_le_one (L H : Matrix n n ℂ)
    (hL : L.PosSemidef) (hH : H.PosSemidef) {γ τ : ℝ}
    (hγ : 0 < γ) (hτ : 0 < τ) (t : ℝ) (ht : 0 ≤ t) (k : ℕ) :
    ‖airyCosineNumerator L H (t : ℂ) (cosineSamplePole γ τ k)‖ ≤ 1 := by
  rw [airyCosineNumerator_sample]
  exact airyPropagator_posSemidef_norm_le_one _
    (cosineSampleMatrix_posSemidef L H hL hH hγ hτ k) t ht

end Matrix
end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
