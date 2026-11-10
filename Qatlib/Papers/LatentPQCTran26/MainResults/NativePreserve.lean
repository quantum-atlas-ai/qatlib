/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LatentPQCTran26.MainResults.ConcentratedMLP
import Mathlib.MeasureTheory.Integral.Average
set_option warningAsError false

noncomputable section
open MeasureTheory
namespace Qatlib.Papers.LatentPQCTran26.MainResults.NativePreserve
open EuclideanLayer LinearMetaGrad ConcentratedMLP NoBiasBarrenPlateau

theorem tanh_pointwise {K d : ℕ}
    (a : (Fin d → ℝ) →L[ℝ] ℝ) (c : ℝ)
    (L : EuclideanSpace ℝ (Fin K) → ℝ)
    (theta v : EuclideanSpace ℝ (Fin K)) (hv : ‖v‖ ≤ 1)
    (Lambda gamma g : ℝ) (hLambda : 0 < Lambda) (hgamma0 : 0 ≤ gamma)
    (hLip : ∀ x y, ‖fderiv ℝ L x - fderiv ℝ L y‖ ≤ Lambda * ‖x - y‖)
    (hg : g ≤ ‖gradient L theta‖) (hgamma : gamma ≤ g / (2 * Lambda))
    (z : Fin d → ℝ) :
    g / 2 ≤ ‖gradient L (decoder K 1 (feature a c z) (weights theta v gamma))‖ := by
  rw [nativeGradient_norm] at hg ⊢
  have hn := output_radius theta v gamma hgamma0 hv a c z
  have hl := (hLip (decoder K 1 (feature a c z) (weights theta v gamma)) theta).trans
    (mul_le_mul_of_nonneg_left hn hLambda.le)
  have hb := norm_le_norm_add_norm_sub
    (fderiv ℝ L (decoder K 1 (feature a c z) (weights theta v gamma))) (fderiv ℝ L theta)
  have hr := radius_arithmetic g Lambda gamma hLambda hgamma
  linarith

theorem tanh_expected {K d : ℕ}
    (r : Measure (Fin d → ℝ)) [IsProbabilityMeasure r]
    (a : (Fin d → ℝ) →L[ℝ] ℝ) (c : ℝ)
    (L : EuclideanSpace ℝ (Fin K) → ℝ) (hD : Continuous (fderiv ℝ L))
    (C : ℝ) (hC : ∀ x, ‖fderiv ℝ L x‖ ≤ C)
    (theta v : EuclideanSpace ℝ (Fin K)) (hv : ‖v‖ ≤ 1)
    (Lambda gamma g : ℝ) (hLambda : 0 < Lambda) (hgamma0 : 0 ≤ gamma) (hg0 : 0 ≤ g)
    (hLip : ∀ x y, ‖fderiv ℝ L x - fderiv ℝ L y‖ ≤ Lambda * ‖x - y‖)
    (hg : g ≤ ‖gradient L theta‖) (hgamma : gamma ≤ g / (2 * Lambda)) :
    g^2/4 ≤ ∫ z, ‖gradient L (decoder K 1 (feature a c z) (weights theta v gamma))‖^2 ∂r := by
  have hc0 : 0 ≤ C := (norm_nonneg (fderiv ℝ L 0)).trans (hC 0)
  have hgen : Continuous (fun z : Fin d → ℝ =>
      decoder K 1 (feature a c z) (weights theta v gamma)) :=
    (decoder_continuous K 1).clm_apply continuous_const |>.comp (feature_continuous a c)
  have hmeas : AEStronglyMeasurable (fun z =>
      ‖gradient L (decoder K 1 (feature a c z) (weights theta v gamma))‖^2) r := by
    simp only [nativeGradient_norm]
    exact ((hD.comp hgen).norm.pow 2).aestronglyMeasurable
  have hint : Integrable (fun z =>
      ‖gradient L (decoder K 1 (feature a c z) (weights theta v gamma))‖^2) r := by
    apply (integrable_const (C^2)).mono' hmeas
    filter_upwards [] with z
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),nativeGradient_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC _) 2
  have hb := integral_mono_ae (integrable_const (g^2/4)) hint
    (Filter.Eventually.of_forall (fun z => by
      have hp := tanh_pointwise a c L theta v hv Lambda gamma g hLambda hgamma0 hLip hg hgamma z
      have hs :=
          sq_nonneg (‖gradient L (decoder K 1 (feature a c z) (weights theta v gamma))‖ - g/2)
      nlinarith))
  simpa using hb

theorem reference_initialization {K d : ℕ}
    (r : Measure (Fin d → ℝ)) [IsProbabilityMeasure r]
    [MeasurableSpace (EuclideanSpace ℝ (Fin K))]
    (nu : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure nu]
    (a : (Fin d → ℝ) →L[ℝ] ℝ) (c : ℝ)
    (L : EuclideanSpace ℝ (Fin K) → ℝ) (hD : Continuous (fderiv ℝ L))
    (C : ℝ) (hC : ∀ x, ‖fderiv ℝ L x‖ ≤ C)
    (v : EuclideanSpace ℝ (Fin K)) (hv : ‖v‖ ≤ 1)
    (Lambda : ℝ) (hLambda : 0 < Lambda)
    (hLip : ∀ x y, ‖fderiv ℝ L x - fderiv ℝ L y‖ ≤ Lambda * ‖x - y‖)
    (hnu : Integrable (fun x => ‖gradient L x‖^2) nu)
    (mu0 : ℝ) (hmean : mu0 ≤ ∫ x, ‖gradient L x‖^2 ∂nu) :
    ∃ theta : EuclideanSpace ℝ (Fin K),
      mu0 / 4 ≤ ∫ z, ‖gradient L (decoder K 1 (feature a c z)
        (weights theta v (‖gradient L theta‖ / (2*Lambda))))‖^2 ∂r := by
  obtain ⟨theta,htheta⟩ := exists_integral_le hnu
  have hp : mu0 ≤ ‖gradient L theta‖^2 := hmean.trans htheta
  have hg0 : 0 ≤ ‖gradient L theta‖ := norm_nonneg _
  have hbound := tanh_expected r a c L hD C hC theta v hv Lambda
    (‖gradient L theta‖/(2*Lambda)) ‖gradient L theta‖ hLambda
    (div_nonneg hg0 (by positivity)) hg0 hLip (le_refl _) (le_refl _)
  exact ⟨theta,(div_le_div_of_nonneg_right hp (by norm_num)).trans hbound⟩

end Qatlib.Papers.LatentPQCTran26.MainResults.NativePreserve
