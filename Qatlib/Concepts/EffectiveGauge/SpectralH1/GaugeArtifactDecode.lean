/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.GaugeCoordinates

set_option backward.isDefEq.respectTransparency false

/-!
# Gauge Artifact Decode

Spectral H1 constructions for Effective Gauge.
Proves `gaugeArtifactCoefficientL1_nonneg`, `gaugeArtifactCisAccuracy_spec`, `rationalCircleCast_norm_le`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.SpectralH1
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Original `gaugeArtifactCoefficientL1_nonneg` guarantee for the `GaugeArtifactDecode` construction; the complete source hypotheses are retained. -/
theorem gaugeArtifactCoefficientL1_nonneg (artifact : RationalGaugeFourierArtifact) :
    0 ≤ gaugeArtifactCoefficientL1 artifact := by
  apply List.sum_nonneg
  intro value hv
  obtain ⟨record,_,rfl⟩ := List.mem_map.mp hv
  exact Finset.sum_nonneg (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _))

/-- Original `gaugeArtifactCisAccuracy_spec` guarantee for the `GaugeArtifactDecode` construction; the complete source hypotheses are retained. -/
theorem gaugeArtifactCisAccuracy_spec (artifact : RationalGaugeFourierArtifact) (accuracy : ℚ)
    (ha : 0<accuracy) :
    0<gaugeArtifactCisAccuracy artifact accuracy ∧ gaugeArtifactCisAccuracy artifact accuracy ≤ 1 ∧
      4*gaugeArtifactCoefficientL1 artifact*gaugeArtifactCisAccuracy artifact accuracy ≤ accuracy/2 := by
  have hC := gaugeArtifactCoefficientL1_nonneg artifact
  have hden : 0<8*(gaugeArtifactCoefficientL1 artifact+1) := by positivity
  have hd : 0<gaugeArtifactCisAccuracy artifact accuracy := lt_min (by norm_num) (div_pos ha hden)
  have hmul := (le_div_iff₀ hden).mp (min_le_right (1 : ℚ) (accuracy/(8*(gaugeArtifactCoefficientL1 artifact+1))))
  refine ⟨hd,min_le_left _ _,?_⟩
  change 4*gaugeArtifactCoefficientL1 artifact*min 1 (accuracy/(8*(gaugeArtifactCoefficientL1 artifact+1))) ≤ accuracy/2
  change 0<min 1 (accuracy/(8*(gaugeArtifactCoefficientL1 artifact+1))) at hd
  nlinarith

noncomputable section
open scoped Quaternion

/-- Original `rationalCircleCast_norm_le` guarantee for the `GaugeArtifactDecode` construction; the complete source hypotheses are retained. -/
theorem rationalCircleCast_norm_le (value : RationalCircleSample) :
    ‖rationalCircleCast value‖ ≤ ((|value.1|+|value.2| : ℚ) : ℝ) := by
  have h := Complex.norm_le_abs_re_add_abs_im (rationalCircleCast value)
  simpa only [rationalCircleCast,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.add_im,Complex.mul_im,
    mul_zero,mul_one,sub_zero,add_zero,zero_add,Rat.cast_add,Rat.cast_abs] using h

/-- Original `quaternion_norm_le_coordinate_sum` guarantee for the `GaugeArtifactDecode` construction; the complete source hypotheses are retained. -/
theorem quaternion_norm_le_coordinate_sum (q : ℍ) :
    ‖q‖ ≤ ∑ j : Fin 4, |quaternionCoordinateCLM j q| := by
  have hsq := Quaternion.normSq_eq_norm_mul_self q
  rw [Quaternion.normSq_def'] at hsq
  simp only [Fin.sum_univ_succ]
  change ‖q‖ ≤ |q.re|+(|q.imI|+(|q.imJ|+(|q.imK|+0)))
  nlinarith [norm_nonneg q,abs_nonneg q.re,abs_nonneg q.imI,abs_nonneg q.imJ,abs_nonneg q.imK,
    sq_abs q.re,sq_abs q.imI,sq_abs q.imJ,sq_abs q.imK,
    mul_nonneg (abs_nonneg q.re) (abs_nonneg q.imI),
    mul_nonneg (abs_nonneg q.re) (abs_nonneg q.imJ),
    mul_nonneg (abs_nonneg q.re) (abs_nonneg q.imK),
    mul_nonneg (abs_nonneg q.imI) (abs_nonneg q.imJ),
    mul_nonneg (abs_nonneg q.imI) (abs_nonneg q.imK),
    mul_nonneg (abs_nonneg q.imJ) (abs_nonneg q.imK)]

/-- Original `gaugeArtifactPhysicalMode_eq` guarantee for the `GaugeArtifactDecode` construction; the complete source hypotheses are retained. -/
theorem gaugeArtifactPhysicalMode_eq (k : SpatialFrequency) (X : Fin 3 → ℚ) :
    unitFourierMode k (physicalPeriod⁻¹ • rationalSpatialPoint X)=
      complexPhase (rationalWindingAngle k X : ℝ) := by
  rw [unitFourierMode_eq_complexPhase,rationalWindingAngle_cast]
  congr 1
  rw [map_smul,smul_eq_mul,← mul_assoc,mul_inv_cancel₀ physicalPeriod_pos.ne',one_mul]
  simp only [frequencyLinear_apply,windingLinear_apply]

/-- Original `gaugeArtifactDecode_complex_error` guarantee for the `GaugeArtifactDecode` construction; the complete source hypotheses are retained. -/
theorem gaugeArtifactDecode_complex_error (artifact : RationalGaugeFourierArtifact)
    (X : Fin 3 → ℚ) (accuracy : ℚ) (ha : 0<accuracy) (j : Fin 4) :
    ‖(artifact.coefficients.map (fun record => rationalCircleCast (cisPairMul (record.2[j.val])
        (rationalCis (rationalWindingAngle (gaugeArtifactFrequency record.1) X)
          (gaugeArtifactCisAccuracy artifact accuracy)).value))).sum-
      (artifact.coefficients.map (fun record => rationalCircleCast (record.2[j.val])*
        unitFourierMode (gaugeArtifactFrequency record.1) (physicalPeriod⁻¹ • rationalSpatialPoint X))).sum‖ ≤
      (gaugeArtifactCoefficientL1 artifact : ℝ)*(gaugeArtifactCisAccuracy artifact accuracy : ℝ) := by
  let d := gaugeArtifactCisAccuracy artifact accuracy
  have hd := gaugeArtifactCisAccuracy_spec artifact accuracy ha
  have hterm (record : Vector ℤ 3 × Vector RationalCircleSample 4) :
      ‖rationalCircleCast (cisPairMul (record.2[j.val])
        (rationalCis (rationalWindingAngle (gaugeArtifactFrequency record.1) X) d).value)-
        rationalCircleCast (record.2[j.val])*
          unitFourierMode (gaugeArtifactFrequency record.1) (physicalPeriod⁻¹ • rationalSpatialPoint X)‖ ≤
      ((∑ i : Fin 4, (|(record.2[i.val]).1| + |(record.2[i.val]).2|) : ℚ) : ℝ)*(d : ℝ) := by
    have hc := rationalCis_spec (rationalWindingAngle (gaugeArtifactFrequency record.1) X) d hd.1 hd.2.1
    have herr : ‖rationalCircleCast (rationalCis (rationalWindingAngle (gaugeArtifactFrequency record.1) X) d).value-
        unitFourierMode (gaugeArtifactFrequency record.1) (physicalPeriod⁻¹ • rationalSpatialPoint X)‖ ≤ (d : ℝ) := by
      rw [gaugeArtifactPhysicalMode_eq]
      exact hc.1.trans (Rat.cast_le.mpr hc.2.2.1)
    have hcoeff : ‖rationalCircleCast (record.2[j.val])‖ ≤
        ((∑ i : Fin 4, (|(record.2[i.val]).1| + |(record.2[i.val]).2|) : ℚ) : ℝ) := by
      apply (rationalCircleCast_norm_le _).trans
      apply Rat.cast_le.mpr
      exact Finset.single_le_sum
        (f := fun i : Fin 4 => (|(record.2[i.val]).1| + |(record.2[i.val]).2|))
        (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ j)
    rw [cisPairMul_cast,← mul_sub,norm_mul]
    exact mul_le_mul hcoeff herr (norm_nonneg _) (by positivity)
  have hsum : ∀ records : RationalGaugeFourierCoefficients,
      ‖(records.map (fun record => rationalCircleCast (cisPairMul (record.2[j.val])
        (rationalCis (rationalWindingAngle (gaugeArtifactFrequency record.1) X) d).value))).sum-
        (records.map (fun record => rationalCircleCast (record.2[j.val])*
          unitFourierMode (gaugeArtifactFrequency record.1) (physicalPeriod⁻¹ • rationalSpatialPoint X))).sum‖ ≤
        (((records.map (fun record => ∑ i : Fin 4, (|(record.2[i.val]).1| + |(record.2[i.val]).2|))).sum : ℚ) : ℝ)*(d : ℝ) := by
    intro records
    induction records with
    | nil => simp
    | cons record records ih =>
      simp only [List.map_cons,List.sum_cons,Rat.cast_add,add_mul]
      have ht := hterm record
      have htri := norm_add_le
        (rationalCircleCast (cisPairMul (record.2[j.val])
          (rationalCis (rationalWindingAngle (gaugeArtifactFrequency record.1) X) d).value)-
            rationalCircleCast (record.2[j.val])*unitFourierMode (gaugeArtifactFrequency record.1)
              (physicalPeriod⁻¹ • rationalSpatialPoint X))
        ((records.map (fun record => rationalCircleCast (cisPairMul (record.2[j.val])
          (rationalCis (rationalWindingAngle (gaugeArtifactFrequency record.1) X) d).value))).sum-
          (records.map (fun record => rationalCircleCast (record.2[j.val])*
            unitFourierMode (gaugeArtifactFrequency record.1) (physicalPeriod⁻¹ • rationalSpatialPoint X))).sum)
      convert htri.trans (add_le_add ht ih) using 1
      ring
  exact hsum artifact.coefficients

/-- Original `gaugeArtifactField_coordinate` guarantee for the `GaugeArtifactDecode` construction; the complete source hypotheses are retained. -/
theorem gaugeArtifactField_coordinate (artifact : RationalGaugeFourierArtifact)
    (X : SpatialPoint) (j : Fin 4) :
    quaternionCoordinateCLM j (gaugeFourierArtifactField artifact X)=
      ((artifact.coefficients.map (fun record => rationalCircleCast (record.2[j.val])*
        unitFourierMode (gaugeArtifactFrequency record.1) (physicalPeriod⁻¹ • X))).sum).re := by
  fin_cases j <;> rfl

/-- Original `gaugeArtifactValue_coordinate` guarantee for the `GaugeArtifactDecode` construction; the complete source hypotheses are retained. -/
theorem gaugeArtifactValue_coordinate (artifact : RationalGaugeFourierArtifact)
    (X : Fin 3 → ℚ) (accuracy : ℚ) (j : Fin 4) :
    quaternionCoordinateCLM j (rationalQuaternionCast (gaugeFourierArtifactValue artifact X accuracy))=
      ((artifact.coefficients.map (fun record => rationalCircleCast (cisPairMul (record.2[j.val])
        (rationalCis (rationalWindingAngle (gaugeArtifactFrequency record.1) X)
          (gaugeArtifactCisAccuracy artifact accuracy)).value))).sum).re := by
  rw [← rationalQuaternionCoordinate_cast]
  have hid : rationalQuaternionCoordinate (gaugeFourierArtifactValue artifact X accuracy) j=
      ((artifact.coefficients.map (fun record => cisPairMul (record.2[j.val])
        (rationalCis (rationalWindingAngle (gaugeArtifactFrequency record.1) X)
          (gaugeArtifactCisAccuracy artifact accuracy)).value)).sum).1 := by
    fin_cases j <;> simp [gaugeFourierArtifactValue,rationalQuaternionCoordinate,List.map_map,Function.comp_def]
  rw [hid]
  have h := congrArg Complex.re (rationalCircleCast_list_sum
    (artifact.coefficients.map (fun record => cisPairMul (record.2[j.val])
      (rationalCis (rationalWindingAngle (gaugeArtifactFrequency record.1) X)
        (gaugeArtifactCisAccuracy artifact accuracy)).value)))
  simpa [List.map_map,Function.comp_def,rationalCircleCast] using h

/-- Any saved artifact, any rational physical address and any positive
decoder accuracy. This bound is relative to its exact finite polynomial,
independently of the producer's approximation error to the canonical Q. -/
theorem gaugeFourierArtifactValue_error (artifact : RationalGaugeFourierArtifact)
    (X : Fin 3 → ℚ) (accuracy : ℚ) (ha : 0<accuracy) :
    ‖rationalQuaternionCast (gaugeFourierArtifactValue artifact X accuracy)-
      gaugeFourierArtifactField artifact (rationalSpatialPoint X)‖ ≤ (accuracy : ℝ)/2 := by
  let C : ℝ := gaugeArtifactCoefficientL1 artifact
  let d : ℝ := gaugeArtifactCisAccuracy artifact accuracy
  have hcoord (j : Fin 4) :
      |quaternionCoordinateCLM j (rationalQuaternionCast (gaugeFourierArtifactValue artifact X accuracy)-
        gaugeFourierArtifactField artifact (rationalSpatialPoint X))| ≤ C*d := by
    rw [map_sub,gaugeArtifactValue_coordinate,gaugeArtifactField_coordinate,← Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans (gaugeArtifactDecode_complex_error artifact X accuracy ha j)
  have hsum := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 4))) => hcoord j)
  have hfour : ∑ _j : Fin 4, C*d=4*C*d := by simp; ring
  have hbudget : 4*C*d ≤ (accuracy : ℝ)/2 := by
    dsimp only [C,d]
    exact_mod_cast (gaugeArtifactCisAccuracy_spec artifact accuracy ha).2.2
  exact (quaternion_norm_le_coordinate_sum _).trans (hsum.trans (hfour.le.trans hbudget))

end
end Qatlib.Concepts.EffectiveGauge.SpectralH1
