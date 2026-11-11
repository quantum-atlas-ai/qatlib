/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.SpectralH1.GaugeArtifactDecode
import Qatlib.Concepts.EffectiveGauge.RationalFlow.GaugeGridExecution
import Qatlib.Concepts.EffectiveGauge.TorusFourier.FourierFiniteCoefficient

set_option backward.isDefEq.respectTransparency false

/-!
# Gauge Artifact Polynomial

Spectral H1 constructions for Effective Gauge.
Defines `quaternionTupleCLM`.
Proves `contDiff_quaternion_components`, `gaugeFourierArtifactField_contDiff`, `gaugeFourierArtifactField_periodic`.
-/

set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff
namespace Qatlib.Concepts.EffectiveGauge.SpectralH1
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Definition of quaternion Tuple CLM in the Spectral H1 construction. -/
def quaternionTupleCLM : (Fin 4 → ℝ) →L[ℝ] ℍ :=
  Quaternion.linearIsometryEquivTuple.symm.toContinuousLinearMap.comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm.toContinuousLinearMap

/-- Original `contDiff_quaternion_components` guarantee for the `GaugeArtifactPolynomial` construction; the complete source hypotheses are retained. -/
theorem contDiff_quaternion_components (c : Fin 4 → SpatialPoint → ℝ)
    (hc : ∀ j, ContDiff ℝ ∞ (c j)) :
    ContDiff ℝ ∞ (fun x : SpatialPoint => quaternionTupleCLM (fun j => c j x)) :=
  quaternionTupleCLM.contDiff.comp (contDiff_pi.mpr hc)

/-- Original `gaugeFourierArtifactField_contDiff` guarantee for the `GaugeArtifactPolynomial` construction; the complete source hypotheses are retained. -/
theorem gaugeFourierArtifactField_contDiff (artifact : RationalGaugeFourierArtifact) :
    ContDiff ℝ ∞ (gaugeFourierArtifactField artifact) := by
  have hs (j : Fin 4) (records : RationalGaugeFourierCoefficients) :
      ContDiff ℝ ∞ (fun X => (records.map (fun record => rationalCircleCast (record.2[j.val])*
        unitFourierMode (gaugeArtifactFrequency record.1) (physicalPeriod⁻¹ • X))).sum) := by
    induction records with
    | nil => simpa only [List.map_nil,List.sum_nil] using (contDiff_const : ContDiff ℝ ∞ (fun _ : SpatialPoint => (0 : ℂ)))
    | cons record records ih =>
      simp only [List.map_cons,List.sum_cons]
      exact (contDiff_const.mul ((contDiff_unitFourierMode _).comp
        (contDiff_id.const_smul physicalPeriod⁻¹))).add ih
  exact contDiff_quaternion_components _ (fun j => Complex.reCLM.contDiff.comp (hs j artifact.coefficients))

/-- Original `gaugeFourierArtifactField_periodic` guarantee for the `GaugeArtifactPolynomial` construction; the complete source hypotheses are retained. -/
theorem gaugeFourierArtifactField_periodic (artifact : RationalGaugeFourierArtifact) :
    IsPeriodicField (gaugeFourierArtifactField artifact) := by
  intro X n
  have hshift : physicalPeriod⁻¹ • (X+latticeShift n)=
      physicalPeriod⁻¹ • X+unitIntegerShift n := by
    ext j
    simp only [PiLp.smul_apply,PiLp.add_apply,latticeShift,unitIntegerShift,
      smul_eq_mul]
    field_simp [physicalPeriod_pos.ne']
  have hcoord (j : Fin 4) :
      quaternionCoordinateCLM j (gaugeFourierArtifactField artifact (X+latticeShift n))=
        quaternionCoordinateCLM j (gaugeFourierArtifactField artifact X) := by
    rw [gaugeArtifactField_coordinate,gaugeArtifactField_coordinate,hshift]
    congr 2
    apply List.map_congr_left
    intro record _
    rw [unitFourierMode_periodic]
  apply Quaternion.ext
  · exact hcoord 0
  · exact hcoord 1
  · exact hcoord 2
  · exact hcoord 3

/-- Original `sourceFrequencyGrid_sum` guarantee for the `GaugeArtifactPolynomial` construction; the complete source hypotheses are retained. -/
theorem sourceFrequencyGrid_sum (N : ℕ) (g : SpatialFrequency → ℂ) :
    ((sourceFrequencyGrid N).map g).sum=∑ k∈Finset.Icc (-N : SpatialFrequency) N, g k := by
  rw [← List.sum_toFinset g (sourceFrequencyGrid_nodup N),sourceFrequencyGrid_toFinset]

/-- The exact saved vectors identify the artifact meaning with the real
part of the finite Fourier polynomial using those same coefficients. -/
theorem gaugeArtifactField_coordinate_truncation (artifact : RationalGaugeFourierArtifact)
    (N M : ℕ) (length d : ℚ) (data : RationalGaugeGridData)
    (hrows : artifact.coefficients=(sourceFrequencyGrid N).map (fun k =>
      (Vector.ofFn k,Vector.ofFn (rationalGaugeFourierCoefficientsOfData M length k d data))))
    (j : Fin 4) (u : SpatialPoint) :
    quaternionCoordinateCLM j (gaugeFourierArtifactField artifact (physicalPeriod • u))=
      (unitFourierTruncation (fun k => rationalCircleCast
        (rationalGaugeFourierCoefficientsOfData M length k d data j)) N u).re := by
  rw [gaugeArtifactField_coordinate,hrows]
  rw [smul_smul,inv_mul_cancel₀ physicalPeriod_pos.ne',one_smul]
  simp only [List.map_map,Function.comp_def,gaugeArtifactFrequency_ofFn,Vector.getElem_ofFn]
  rw [sourceFrequencyGrid_sum]
  rfl

end Qatlib.Concepts.EffectiveGauge.SpectralH1
