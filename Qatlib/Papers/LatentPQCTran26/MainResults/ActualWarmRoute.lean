/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic

noncomputable section
open MeasureTheory
namespace Qatlib.Papers.LatentPQCTran26.MainResults.ActualWarmRoute
variable {Theta : Type*} [MeasurableSpace Theta]

def prior (nu train : Measure Theta) (lam : NNReal) : Measure (Theta ⊕ Theta) :=
  lam • nu.map Sum.inl + (1-lam) • train.map Sum.inr

def route : Theta ⊕ Theta → Theta := Sum.elim id id

theorem route_measurable : Measurable (route (Theta := Theta)) :=
  measurable_id.sumElim measurable_id

theorem pushforward (nu train : Measure Theta) (lam : NNReal) :
    (prior nu train lam).map route = lam • nu + (1-lam) • train := by
  rw [prior, Measure.map_add _ _ route_measurable,
    Measure.map_smul _ route_measurable.aemeasurable,
    Measure.map_smul _ route_measurable.aemeasurable,
    Measure.map_map route_measurable measurable_inl,
    Measure.map_map route_measurable measurable_inr]
  simp [route,Function.comp_def]

theorem prior_isProbability (nu train : Measure Theta) [IsProbabilityMeasure nu]
    [IsProbabilityMeasure train] (lam : NNReal) (hlam : lam ≤ 1) :
    IsProbabilityMeasure (prior nu train lam) := by
  apply isProbabilityMeasure_iff.mpr
  simp only [prior,Measure.add_apply,Measure.smul_apply,Measure.map_apply measurable_inl
    MeasurableSet.univ,Set.preimage_univ,measure_univ,
    Measure.map_apply measurable_inr MeasurableSet.univ]
  have h : lam + (1-lam) = (1 : NNReal) := add_tsub_cancel_of_le hlam
  change (lam : ENNReal) * 1 + ((1-lam : NNReal) : ENNReal) * 1 = 1
  simp only [mul_one]
  exact_mod_cast h

theorem native_gradient_transfer
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] (nu train : Measure E) [IsProbabilityMeasure nu]
    [IsProbabilityMeasure train] (lam : NNReal) (L : E → ℝ)
    (hnu : Integrable (fun x => ‖gradient L x‖^2) nu)
    (htrain : Integrable (fun x => ‖gradient L x‖^2) train)
    (hgrad : AEStronglyMeasurable (fun x => ‖gradient L x‖^2) (lam • nu + (1-lam) • train))
    (mu0 : ℝ) (hmean : mu0 ≤ ∫ x, ‖gradient L x‖^2 ∂nu) :
    (lam : ℝ) * mu0 ≤
      ∫ z, ‖gradient L (route z)‖^2 ∂prior nu train lam := by
  have hmap := integral_map (route_measurable (Theta := E)).aemeasurable
    (show AEStronglyMeasurable (fun x => ‖gradient L x‖^2)
      ((prior nu train lam).map route) by rwa [pushforward])
  rw [← hmap,pushforward,integral_add_measure
    (hnu.smul_measure_nnreal (c := lam)) (htrain.smul_measure_nnreal (c := 1-lam)),
    integral_smul_nnreal_measure,integral_smul_nnreal_measure]
  have hn : 0 ≤ ∫ x, ‖gradient L x‖^2 ∂train := integral_nonneg (fun _ => sq_nonneg _)
  have hm := mul_le_mul_of_nonneg_left hmean lam.coe_nonneg
  change (lam : ℝ)*mu0 ≤ (lam : ℝ)*(∫ x, ‖gradient L x‖^2 ∂nu) +
    ((1-lam : NNReal) : ℝ)*(∫ x, ‖gradient L x‖^2 ∂train)
  exact hm.trans (le_add_of_nonneg_right (mul_nonneg (NNReal.coe_nonneg _) hn))

end Qatlib.Papers.LatentPQCTran26.MainResults.ActualWarmRoute
