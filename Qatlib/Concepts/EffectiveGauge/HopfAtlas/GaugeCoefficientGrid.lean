/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.GaugeGridExecution

set_option backward.isDefEq.respectTransparency false

/-!
# Gauge Coefficient Grid

Hopf Atlas constructions for Effective Gauge.
Proves `gaugeGridExecution_coefficient_error`.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped Quaternion ContDiff
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.SpectralH1 Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- The sample callback executes once per node, outside all frequencies
and components. The coefficient errors concern its saved rational data. -/
theorem gaugeGridExecution_coefficient_error (Q : QuaternionField) (hQ : ContDiff ℝ ∞ Q)
    (hp : IsUnitPeriodicField Q) (hnorm : ∀ x, ‖Q x‖ ≤ 1)
    (P1 : ℚ) (hP : 0 ≤ P1)
    (hword : ∀ x i, ‖spatialWordPartial Q [i] x‖ ≤ (P1 : ℝ))
    (M : ℕ) (hM : 0<M)
    (sample : SourceMeanIndex → Option (Quaternion ℚ)) (s : ℚ)
    (hsample : ∀ index, ∃ out, sample index=some out ∧
      ‖rationalQuaternionCast out-Q (rationalSpatialPoint (sourceMeanUnitPoint M index))‖ ≤ (s : ℝ))
    (N : ℕ) (length d : ℚ) (hdpos : 0<d) (hd1 : d ≤ 1) (ell : ℝ)
    (hl : |(length : ℝ)-physicalPeriod| ≤ ell) (hell : 3*(N : ℝ)*ell ≤ (d : ℝ)/2) :
    ∃ data, gaugeGridExecution sample (sourceMeanGrid M)=some data ∧
      data.map Prod.fst=sourceMeanGrid M ∧ ∀ k : SpatialFrequency,
      (∀ i, |(k i : ℝ)| ≤ (N : ℝ)) → ∀ j : Fin 4,
      let f := fun x => quaternionComplexCoordinateCLM j (Q x)
      let hf := (quaternionComplexCoordinateCLM j).contDiff.comp hQ
      let hp' : IsUnitPeriodicField f := fun i x => by dsimp only [f]; rw [hp i x]
      ‖unitFourierCoefficient f hf.continuous hp' k-
        rationalCircleCast (rationalGaugeFourierCoefficientsOfData M length k d data j)‖ ≤
        3*((P1 : ℝ)+7*(N : ℝ))/(M : ℝ)+((s : ℝ)+(1+(s : ℝ))*(d : ℝ)) := by
  let values := gaugeGridNode sample
  let data := (sourceMeanGrid M).map (fun index => (index,values index))
  have hdata : gaugeGridExecution sample (sourceMeanGrid M)=some data :=
    gaugeGridExecution_eq_map sample _ (fun index _ => ⟨_,(hsample index).choose_spec.1⟩)
  refine ⟨data,hdata,?_,?_⟩
  · simp only [data,List.map_map,Function.comp_def,List.map_id_fun']
    rfl
  · intro k hk j
    dsimp only
    let f := fun x => quaternionComplexCoordinateCLM j (Q x)
    have hf : ContDiff ℝ ∞ f := (quaternionComplexCoordinateCLM j).contDiff.comp hQ
    have hp' : IsUnitPeriodicField f := fun i x => by dsimp only [f]; rw [hp i x]
    change ‖unitFourierCoefficient f hf.continuous hp' k-
      rationalCircleCast (rationalGaugeFourierCoefficientsOfData M length k d
        ((sourceMeanGrid M).map (fun index => (index,values index))) j)‖ ≤ _
    rw [rationalGaugeFourierCoefficientsOfData_cast]
    apply (sampledFourierCoefficientGrid_error M hM f hf hp' k N hk 1 (P1 : ℝ)
      (by norm_num) (Rat.cast_nonneg.mpr hP)
      (fun x _ => (quaternionComplexCoordinateCLM_norm_le j _).trans (hnorm x))
      (fun x _ i => quaternionComplexCoordinate_word_bound Q hQ j [i] (P1 : ℝ)
        (fun y => hword y i) x) _ _ (s : ℝ) (d : ℝ) ?_ ?_).trans_eq (by ring)
    · intro a _ b _ c _
      obtain ⟨out,hout,herror⟩ := hsample (a,b,c)
      have he := (quaternionComplexCoordinate_error j (rationalQuaternionCast out)
        (Q (rationalSpatialPoint (sourceMeanUnitPoint M (a,b,c))))).trans herror
      rw [← rationalQuaternionCoordinate_complex_cast] at he
      simpa only [values,gaugeGridNode,hout,Option.getD_some,sourceMeanUnitPoint_cast] using he
    · intro a ha b hb c hc
      have hmem := (sourceMeanGrid_mem M (a,b,c)).mpr ⟨ha,hb,hc⟩
      have hu := sourceMeanUnitPoint_mem M hM (a,b,c) hmem
      have hk' : ∀ i, |((-k) i : ℝ)| ≤ (N : ℝ) := by
        intro i
        simpa only [Pi.neg_apply,Int.cast_neg,abs_neg] using hk i
      have he := rationalFourierMode_error length (-k) (sourceMeanUnitPoint M (a,b,c))
        d hdpos hd1 N hk' hu ell hl
      rw [sourceMeanUnitPoint_cast] at he
      exact he.trans (by linarith)

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
