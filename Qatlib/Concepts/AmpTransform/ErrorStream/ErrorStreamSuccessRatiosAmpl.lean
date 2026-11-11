/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.ErrorStream.ErrorStreamSuccessRatiosStat
import Qatlib.Concepts.AmpTransform.ErrorStream.AmplifiedMarkedSetAmplitudes

/-!
# Amplified success ratios for noisy marked sets

`errorStreamSuccessRatios` establishes the probability ratios between amplified Fourier sampling
and the phase and quantum hidden-subgroup baselines on events excluding the zero frequency. The
result also bounds the common amplification ratio for the noisy-progression setting of
[Cornwell2014].

## Main statements

* `errorStreamSuccessRatios`: Establishes the exact event-level amplified-to-baseline success
  ratios and the stated bounds on `aqRatio` for a noisy progression and events excluding zero;
  see [Cornwell2014].

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option warningAsError false

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.AmpTransform.NoiseEnvelope

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qatlib.Concepts.AmpTransform.ErrorStream
open scoped Classical BigOperators

/-- Establishes the exact event-level amplified-to-baseline success ratios and the stated bounds
on `aqRatio` for a noisy progression and events excluding zero; see [Cornwell2014]. -/
theorem errorStreamSuccessRatios : ErrorStreamSuccessRatios := by
  intro N hN s M L P G h E hM hP hbound h2T hG hdis hmark hzero
  (try dsimp only)
  let C := aqProgressionSet N s M P ∪ G
  let T := M+L
  have hTpos : 0 < T := by dsimp [T]; omega
  have hcard : C.card=T := by
    dsimp [C,T]
    rw [Finset.card_union_of_disjoint hdis.symm,
      aqProgression_card N s M P (by omega) hP hbound, hG]
  have hTR : (T : ℝ) ≠ 0 := by exact_mod_cast hTpos.ne'
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hsub : ((N-T : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show N-T ≠ 0 by dsimp [T]; omega)
  have hpoint (y : Fin N) (hy : y ∈ E) :
      BornProb (aqState N hN T C) y=aqRatio N T*BornProb (aqPhaseBaseline N hN C) y ∧
      BornProb (aqState N hN T C) y=2*aqRatio N T*
        MeasureProb (aqQHSBaseline N hN h) ({y} ×ˢ Finset.univ) := by
    have hy0 : y.val ≠ 0 := by
      intro hv
      apply hzero
      exact (Fin.ext hv : y=(⟨0,hN⟩ : Fin N)) ▸ hy
    have hp := aq_marked_three_probabilities N hN T C h y hTpos hcard h2T hmark hy0
    rw [hp.1, hp.2.1, hp.2.2, aq_tan_density N T hN hTpos h2T]
    unfold aqRatio
    constructor
    · field_simp
    · field_simp
      norm_num
  have hevents : MeasureProb (aqState N hN T C) E=
      aqRatio N T*MeasureProb (aqPhaseBaseline N hN C) E ∧
      MeasureProb (aqState N hN T C) E=2*aqRatio N T*
        MeasureProb (aqQHSBaseline N hN h) (E ×ˢ Finset.univ) := by
    by_cases hGe : G=∅
    · have hL : L=0 := by simpa [hGe] using! hG.symm
      have hm : AQMarkPromise h s M P := by
        intro x
        simpa [hGe] using! hmark x
      have hr := amplified_progression_success_event_probability_ratios
        N hN s M P h E hM hP hbound (by simpa [hL] using! h2T) hm hzero
      simpa [C, T, hGe, hL] using! hr
    · constructor
      · change (∑ y ∈ E, BornProb (aqState N hN T C) y)=
          aqRatio N T*∑ y ∈ E, BornProb (aqPhaseBaseline N hN C) y
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun y hy => (hpoint y hy).1)
      · have hs : MeasureProb (aqQHSBaseline N hN h) (E ×ˢ Finset.univ)=
            ∑ y ∈ E, MeasureProb (aqQHSBaseline N hN h) ({y} ×ˢ Finset.univ) := by
          simp only [MeasureProb, Finset.sum_product, Finset.sum_singleton]
        rw [hs, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun y hy => (hpoint y hy).2)
  refine ⟨hevents.1, hevents.2, ?_, ?_⟩
  · have ht := aq_angle_properties N T hN hTpos h2T
    have hg := aq_floor_gain (aqAngle N T) ht.1 ht.2.1
    have hc : Real.cos (2*aqAngle N T)=1-2*(T : ℝ)/(N : ℝ) := by
      rw [Real.cos_two_mul]
      have he := Real.sin_sq_add_cos_sq (aqAngle N T)
      rw [ht.2.2.2.1] at he
      simp only [mul_div_assoc]
      linarith
    have hlower : (1-2*(T : ℝ)/(N : ℝ))^2 ≤ aqGain N T := by
      rw [← hc]
      exact hg.2.1
    have hmul := mul_le_mul_of_nonneg_left hlower
      (by positivity : 0 ≤ (N : ℝ)^2/(4*(T : ℝ)*((N-T : ℕ) : ℝ)))
    unfold aqRatio
    convert! hmul using 1
    ring
  · have ht := aq_angle_properties N T hN hTpos h2T
    have hg := aq_floor_gain (aqAngle N T) ht.1 ht.2.1
    have hgain : aqGain N T ≤ 1 := hg.2.2
    have hmul := mul_le_mul_of_nonneg_left hgain
      (by positivity : 0 ≤ (N : ℝ)^2/(4*(T : ℝ)*((N-T : ℕ) : ℝ)))
    unfold aqRatio
    change (N : ℝ)^2*aqGain N T/(4*(T : ℝ)*((N-T : ℕ) : ℝ)) ≤ _
    convert! hmul using 1 <;> ring

end Qatlib.Concepts.AmpTransform.ErrorStream
