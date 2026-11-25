/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.Forrelation14.MainResults.ForrelationModel
public import Qatlib.Papers.KForrelation20.MainResults.GaussianTools.GaussianConcentration
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

/-!
# Gaussian data in Proposition 12

The choice of threshold in arXiv:1411.5729v1 gives a uniform failure bound
for each standard Gaussian coordinate and for their finite union.
-/

set_option autoImplicit false

open scoped BigOperators
open MeasureTheory ProbabilityTheory
open Qatlib.Papers.Forrelation14.MainResults
open Qatlib.Papers.KForrelation20.MainResults

namespace Qatlib.Papers.Forrelation14.MainResults

/-- Above a positive threshold the standard Gaussian measure is bounded
by half of the corresponding exponential. -/
private theorem standard_gauss_upper_tail {a : ℝ} (ha : 0 < a) :
    (gaussianReal 0 1).real (Set.Ioi a) ≤ 2⁻¹ * Real.exp (-(a ^ 2) / 2) := by
  have hd (x : ℝ) : gaussianPDFReal 0 1 x = gaussDensity x := by
    simp [gaussianPDFReal, gaussDensity]
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero]
  simp_rw [hd]
  rw [ENNReal.toReal_ofReal (integral_nonneg fun x => gaussDensity_nonneg x)]
  have h := gaussCdf_add_gaussTail a
  have hb := gaussianConcentration ha
  change gaussTail a ≤ _
  linarith only [h, hb]

/-- The two-sided tail of a standard Gaussian at a positive threshold. -/
theorem standard_gauss_abs_tail {a : ℝ} (ha : 0 < a) :
    (gaussianReal 0 1).real {x | a < |x|} ≤ Real.exp (-(a ^ 2) / 2) := by
  have hs : {x : ℝ | a < |x|} = Set.Iio (-a) ∪ Set.Ioi a := by
    ext x
    simp [lt_abs, or_comm, lt_neg]
  have hneg : (gaussianReal 0 1).real (Set.Iio (-a)) =
      (gaussianReal 0 1).real (Set.Ioi a) := by
    have hmap : (gaussianReal 0 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
      simpa using gaussianReal_map_neg (μ := 0) (v := 1)
    have hpre : (fun x : ℝ => -x) ⁻¹' Set.Ioi a = Set.Iio (-a) := by
      ext x
      simp
    conv_rhs => rw [← hmap]
    rw [measureReal_def, measureReal_def, Measure.map_apply (by fun_prop) measurableSet_Ioi, hpre]
  rw [hs]
  have h := standard_gauss_upper_tail ha
  exact (measureReal_union_le _ _).trans (by rw [hneg]; linarith only [h])

/-- Each evaluation map on the finite Gaussian product has standard
Gaussian law. -/
private theorem gaussLaw_eval_real {t : ℕ} (i : Fin t) (s : Set ℝ) (hs : MeasurableSet s) :
    (Model.gaussLaw t).real ((fun a : Model.Vec t => a i) ⁻¹' s) =
      (gaussianReal 0 1).real s := by
  have h := measurePreserving_eval (fun _ : Fin t => gaussianReal 0 1) i
  exact congrArg ENNReal.toReal (h.measure_preimage hs.nullMeasurableSet)

/-- The failure event defined in Proposition 12 has probability at most
1/100 under the finite product of standard Gaussian laws. -/
theorem prop12_gauss_failure_le (t : ℕ) (ht : 0 < t) :
    Model.gaussProb t (fun a => ¬ Model.WellBehaved a) ≤ 1 / 100 := by
  let a : ℝ := Real.sqrt (2 * Real.log (100 * (t : ℝ)))
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have ht₁ : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have ha : 0 < a := Real.sqrt_pos.2 (mul_pos (by norm_num)
    (Real.log_pos (by linarith)))
  let s : Fin t → Set (Model.Vec t) := fun i => (fun x : Model.Vec t => x i) ⁻¹' {x | a < |x|}
  have hs : MeasurableSet {x : ℝ | a < |x|} := measurableSet_lt measurable_const (by fun_prop)
  have hevent : {x : Model.Vec t | ¬ Model.WellBehaved x} = ⋃ i, s i := by
    ext x
    simp [Model.WellBehaved, s, a]
  have hexp : Real.exp (-(a ^ 2) / 2) = 1 / (100 * (t : ℝ)) := by
    dsimp [a]
    rw [Real.sq_sqrt (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith)))]
    rw [show -(2 * Real.log (100 * (t : ℝ))) / 2 = -Real.log (100 * t) by ring,
      Real.exp_neg, Real.exp_log (by positivity), one_div]
  have hbound (i : Fin t) : (Model.gaussLaw t).real (s i) ≤ 1 / (100 * (t : ℝ)) := by
    rw [gaussLaw_eval_real i _ hs, ← hexp]
    exact standard_gauss_abs_tail ha
  let : IsProbabilityMeasure (Model.gaussLaw t) := by
    unfold Model.gaussLaw Model.gaussMeasure
    infer_instance
  change (Model.gaussLaw t).real {x | ¬ Model.WellBehaved x} ≤ _
  rw [hevent]
  calc
    _ ≤ ∑ i, (Model.gaussLaw t).real (s i) := measureReal_iUnion_fintype_le s
    _ ≤ ∑ _ : Fin t, (1 / (100 * (t : ℝ))) := Finset.sum_le_sum fun i _ => hbound i
    _ = _ := by
      simp [nsmul_eq_mul]
      field_simp

/-- The positive-probability form of Proposition 12. -/
theorem prop12_gauss_well_behaved (t : ℕ) (ht : 0 < t) :
    99 / 100 ≤ Model.gaussProb t Model.WellBehaved := by
  let : IsProbabilityMeasure (Model.gaussLaw t) := by
    unfold Model.gaussLaw Model.gaussMeasure
    infer_instance
  have hs : MeasurableSet {x : Model.Vec t | Model.WellBehaved x} := by
    let bound : ℝ := Real.sqrt (2 * Real.log (100 * (t : ℝ)))
    have hset : {x : Model.Vec t | Model.WellBehaved x} =
        ⋂ i : Fin t, {x : Model.Vec t | |x i| ≤ bound} := by
      ext x
      simp [Model.WellBehaved, bound]
    rw [hset]
    exact MeasurableSet.iInter fun i =>
      measurableSet_le (show Measurable (fun x : Model.Vec t => |x i|) by fun_prop) measurable_const
  have h := prop12_gauss_failure_le t ht
  change (Model.gaussLaw t).real ({x : Model.Vec t | Model.WellBehaved x}ᶜ) ≤ _ at h
  rw [measureReal_compl hs, probReal_univ] at h
  change _ ≤ (Model.gaussLaw t).real {x : Model.Vec t | Model.WellBehaved x}
  linarith

end Qatlib.Papers.Forrelation14.MainResults
