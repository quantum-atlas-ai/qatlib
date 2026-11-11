/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.SpectralH1.GaugeArtifactH1Bound

set_option backward.isDefEq.respectTransparency false

/-!
# Gauge Artifact Physical H1

Spectral H1 constructions for Effective Gauge.
Proves `gaugeArtifact_physical_H1_bound`.
-/

set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff
namespace Qatlib.Concepts.EffectiveGauge.SpectralH1
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Original `gaugeArtifact_physical_H1_bound` guarantee for the `GaugeArtifactPhysicalH1` construction; the complete source hypotheses are retained. -/
theorem gaugeArtifact_physical_H1_bound (Q : QuaternionField) (hQ : ContDiff ℝ ∞ Q)
    (hp : IsPeriodicField Q) (artifact : RationalGaugeFourierArtifact)
    (N M : ℕ) (length d : ℚ) (data : RationalGaugeGridData)
    (hrows : artifact.coefficients=(sourceFrequencyGrid N).map (fun k =>
      (Vector.ofFn k,Vector.ofFn (rationalGaugeFourierCoefficientsOfData M length k d data))))
    (delta M3 : ℝ) (hd : 0 ≤ delta) (hM : 0 ≤ M3)
    (hcoef : ∀ j : Fin 4,
      let G := fun u => Q (physicalPeriod • u)
      let f := fun u => quaternionComplexCoordinateCLM j (G u)
      let hf := (quaternionComplexCoordinateCLM j).contDiff.comp (hQ.comp (contDiff_id.const_smul physicalPeriod))
      let hp' : IsUnitPeriodicField f := fun u n => by
        exact congrArg (quaternionComplexCoordinateCLM j) (periodicField_rescale_unit Q hp u n)
      ∀ k∈Finset.Icc (-N : SpatialFrequency) N,
        ‖unitFourierCoefficient f hf.continuous hp' k-rationalCircleCast
          (rationalGaugeFourierCoefficientsOfData M length k d data j)‖ ≤ delta)
    (hthird : ∀ i u, ‖spatialWordPartial (fun u => Q (physicalPeriod • u)) [i,i,i] u‖ ≤ M3) :
    physicalFieldH1Energy (fun X => Q X-gaugeFourierArtifactField artifact X) ≤
      4*343*(((2*N+1)^3 : ℕ) : ℝ)*(1+3*(N : ℝ)^2)*delta^2+
        48*M3^2/((N : ℝ)+1)^4 := by
  let G := fun u => Q (physicalPeriod • u)
  have hG : ContDiff ℝ ∞ G := hQ.comp (contDiff_id.const_smul physicalPeriod)
  have hGp : IsUnitPeriodicField G := periodicField_rescale_unit Q hp
  have hu := gaugeArtifact_normalized_H1_bound G hG hGp artifact N M length d data hrows delta M3 hd hM hcoef hthird
  have he := physicalFieldH1Energy_scale (fun X => Q X-gaugeFourierArtifactField artifact X)
    (hQ.sub (gaugeFourierArtifactField_contDiff artifact))
  rw [he]
  apply (mul_le_mul_of_nonneg_left hu (pow_nonneg physicalPeriod_pos.le 3)).trans
  let J : ℝ := ((2*N+1)^3 : ℕ)
  let D : ℝ := ((N : ℝ)+1)^4
  have hD : 0<D := by positivity
  have hL1 : (1 : ℝ) ≤ physicalPeriod := by dsimp only [physicalPeriod]; linarith [Real.pi_gt_three]
  have hL7 : physicalPeriod ≤ 7 := by dsimp only [physicalPeriod]; linarith [Real.pi_lt_d2]
  have hL3 : (1 : ℝ) ≤ physicalPeriod^3 := one_le_pow₀ hL1
  have hL3upper : physicalPeriod^3 ≤ 343 := by
    have h := pow_le_pow_left₀ physicalPeriod_pos.le hL7 3
    norm_num at h
    exact h
  have hid : physicalPeriod^3*(4*(J*(1+3*(N : ℝ)^2)*delta^2+
      12*M3^2/(physicalPeriod^6*D)))=
      4*physicalPeriod^3*J*(1+3*(N : ℝ)^2)*delta^2+48*M3^2/(physicalPeriod^3*D) := by
    field_simp [physicalPeriod_pos.ne',hD.ne']
    ring
  change physicalPeriod^3*(4*(J*(1+3*(N : ℝ)^2)*delta^2+
      12*M3^2/(physicalPeriod^6*D))) ≤ 4*343*J*(1+3*(N : ℝ)^2)*delta^2+48*M3^2/D
  rw [hid]
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL3upper (by norm_num)) (by positivity))
      (by positivity)) (sq_nonneg delta)
  · apply div_le_div₀ (by positivity) le_rfl hD
    nlinarith [mul_le_mul_of_nonneg_right hL3 hD.le]

end Qatlib.Concepts.EffectiveGauge.SpectralH1
