/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.FourierModeBounds
import Mathlib.Analysis.Calculus.SmoothSeries

set_option backward.isDefEq.respectTransparency false

/-!
# Fourier Series

Torus Fourier constructions for Effective Gauge.
Defines `unitFourierSeries`, `FourierRapidlySummable`.
Proves `unitFourierTerm_iteratedFDeriv_norm_le`, `unitFourierSeries_contDiff`, `unitFourierSeries_iteratedFDeriv`.
-/


set_option autoImplicit false
noncomputable section
open Finset
open scoped ContDiff Topology
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of unit Fourier Series in the Torus Fourier construction. -/
def unitFourierSeries (a : SpatialFrequency → ℂ) (x : SpatialPoint) : ℂ :=
  ∑' k : SpatialFrequency, a k*unitFourierMode k x

/-- Definition of Fourier Rapidly Summable in the Torus Fourier construction. -/
def FourierRapidlySummable (a : SpatialFrequency → ℂ) : Prop :=
  ∀ n : ℕ, Summable (fun k : SpatialFrequency => (frequencyRadius k : ℝ)^n*‖a k‖)

/-- Original `unitFourierTerm_iteratedFDeriv_norm_le` guarantee for the `FourierSeries` construction; the complete source hypotheses are retained. -/
theorem unitFourierTerm_iteratedFDeriv_norm_le (a : SpatialFrequency → ℂ)
    (n : ℕ) (k : SpatialFrequency) (x : SpatialPoint) :
    ‖iteratedFDeriv ℝ n (fun y => a k*unitFourierMode k y) x‖ ≤
      (3*physicalPeriod)^n*((frequencyRadius k : ℝ)^n*‖a k‖) := by
  let B : ℂ →L[ℝ] ℂ := (ContinuousLinearMap.mul ℝ ℂ) (a k)
  have hB : ‖B‖ ≤ ‖a k‖ := by
    apply B.opNorm_le_bound (norm_nonneg _)
    intro z
    exact le_of_eq (norm_mul (a k) z)
  change ‖iteratedFDeriv ℝ n (B ∘ unitFourierMode k) x‖ ≤ _
  calc
    _ ≤ ‖B‖*‖iteratedFDeriv ℝ n (unitFourierMode k) x‖ :=
      B.norm_iteratedFDeriv_comp_left (contDiff_unitFourierMode k).contDiffAt
        (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
    _ ≤ ‖a k‖*(3*physicalPeriod*(frequencyRadius k : ℝ))^n := by
      apply mul_le_mul hB _ (norm_nonneg _) (norm_nonneg _)
      exact (unitFourierMode_iteratedFDeriv_norm_le k n x).trans
        (pow_le_pow_left₀ (norm_nonneg _) (fourierModeExponent_norm_le k) n)
    _ = _ := by rw [mul_pow]; ring

/-- Original `unitFourierSeries_contDiff` guarantee for the `FourierSeries` construction; the complete source hypotheses are retained. -/
theorem unitFourierSeries_contDiff (a : SpatialFrequency → ℂ) (ha : FourierRapidlySummable a) :
    ContDiff ℝ ∞ (unitFourierSeries a) := by
  apply contDiff_tsum (N := ⊤)
    (fun k => contDiff_const.mul (contDiff_unitFourierMode k))
    (v := fun n k => (3*physicalPeriod)^n*((frequencyRadius k : ℝ)^n*‖a k‖))
  · intro n hn
    exact (ha n).mul_left _
  · intro n k x hn
    exact unitFourierTerm_iteratedFDeriv_norm_le a n k x

/-- Original `unitFourierSeries_iteratedFDeriv` guarantee for the `FourierSeries` construction; the complete source hypotheses are retained. -/
theorem unitFourierSeries_iteratedFDeriv (a : SpatialFrequency → ℂ)
    (ha : FourierRapidlySummable a) (n : ℕ) (x : SpatialPoint) :
    iteratedFDeriv ℝ n (unitFourierSeries a) x=
      ∑' k : SpatialFrequency, iteratedFDeriv ℝ n (fun y => a k*unitFourierMode k y) x := by
  apply iteratedFDeriv_tsum_apply (N := ⊤)
    (fun k => contDiff_const.mul (contDiff_unitFourierMode k))
    (v := fun m k => (3*physicalPeriod)^m*((frequencyRadius k : ℝ)^m*‖a k‖))
  · intro m hm
    exact (ha m).mul_left _
  · intro m k y hm
    exact unitFourierTerm_iteratedFDeriv_norm_le a m k y
  · exact le_top

/-- Original `unitFourierSeries_periodic` guarantee for the `FourierSeries` construction; the complete source hypotheses are retained. -/
theorem unitFourierSeries_periodic (a : SpatialFrequency → ℂ) :
    IsUnitPeriodicField (unitFourierSeries a) := by
  intro x m
  apply tsum_congr
  intro k
  rw [unitFourierMode_periodic k x m]

/-- Original `unitFourierTerm_first` guarantee for the `FourierSeries` construction; the complete source hypotheses are retained. -/
theorem unitFourierTerm_first (a : SpatialFrequency → ℂ) (k : SpatialFrequency) (i : Fin 3) :
    spatialWordPartial (fun x => a k*unitFourierMode k x) [i]=fun x =>
      (((physicalPeriod : ℂ)*Complex.I*(k i : ℂ))*a k)*unitFourierMode k x := by
  let B : ℂ →L[ℝ] ℂ := (ContinuousLinearMap.mul ℝ ℂ) (a k)
  have h := spatialWordPartial_clm B (unitFourierMode k) (contDiff_unitFourierMode k) [i]
  change spatialWordPartial (fun x => a k*unitFourierMode k x) [i]=
    (fun x => a k*spatialWordPartial (unitFourierMode k) [i] x) at h
  rw [h,unitFourierMode_first]
  funext x
  ring

/-- A summable operator derivative bound justifies the actual first
 derivative of the infinite series, before identifying its coefficients. -/
theorem unitFourierSeries_partial (a : SpatialFrequency → ℂ) (ha : FourierRapidlySummable a)
    (i : Fin 3) :
    spatialWordPartial (unitFourierSeries a) [i]=
      unitFourierSeries (fun k => ((physicalPeriod : ℂ)*Complex.I*(k i : ℂ))*a k) := by
  let f := fun k : SpatialFrequency => fun x : SpatialPoint => a k*unitFourierMode k x
  let u := fun k : SpatialFrequency => (3*physicalPeriod)*((frequencyRadius k : ℝ)*‖a k‖)
  have hu : Summable u := by simpa only [pow_one] using (ha 1).mul_left (3*physicalPeriod)
  have hd (k : SpatialFrequency) (x : SpatialPoint) : ‖fderiv ℝ (f k) x‖ ≤ u k := by
    simpa only [norm_iteratedFDeriv_one,pow_one] using
      unitFourierTerm_iteratedFDeriv_norm_le a 1 k x
  have hs0 : Summable (fun k => f k (0 : SpatialPoint)) := by
    apply (ha 0).of_norm_bounded
    intro k
    simp only [f,norm_mul,unitFourierMode_norm,mul_one,pow_zero,one_mul,le_refl]
  funext x
  have h := hasFDerivAt_tsum hu
    (fun k y => ((contDiff_const.mul (contDiff_unitFourierMode k)).differentiable
      (by simp) y).hasFDerivAt) hd hs0 x
  change HasFDerivAt (unitFourierSeries a) (∑' k : SpatialFrequency, fderiv ℝ (f k) x) x at h
  have hsD : Summable (fun k => fderiv ℝ (f k) x) := hu.of_norm_bounded (fun k => hd k x)
  have hm := (ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single i 1)).map_tsum hsD
  change (∑' k : SpatialFrequency, fderiv ℝ (f k) x) (EuclideanSpace.single i 1)=
    ∑' k : SpatialFrequency, fderiv ℝ (f k) x (EuclideanSpace.single i 1) at hm
  change fderiv ℝ (unitFourierSeries a) x (EuclideanSpace.single i 1)=_
  rw [h.fderiv,hm]
  apply tsum_congr
  intro k
  exact congrFun (unitFourierTerm_first a k i) x

/-- Original `FourierRapidlySummable.partial` guarantee for the `FourierSeries` construction; the complete source hypotheses are retained. -/
theorem FourierRapidlySummable.partial {a : SpatialFrequency → ℂ}
    (ha : FourierRapidlySummable a) (i : Fin 3) :
    FourierRapidlySummable (fun k => ((physicalPeriod : ℂ)*Complex.I*(k i : ℂ))*a k) := by
  intro n
  have hs := (ha (n+1)).mul_left physicalPeriod
  apply hs.of_norm_bounded
  intro k
  rw [Real.norm_of_nonneg (by positivity)]
  have hfactor : ‖(physicalPeriod : ℂ)*Complex.I*(k i : ℂ)‖ ≤
      physicalPeriod*(frequencyRadius k : ℝ) := by
    rw [norm_mul,norm_mul,Complex.norm_I,mul_one]
    have hL : ‖(physicalPeriod : ℂ)‖=physicalPeriod := by
      rw [Complex.norm_real,Real.norm_of_nonneg physicalPeriod_pos.le]
    rw [hL]
    apply mul_le_mul_of_nonneg_left _ physicalPeriod_pos.le
    simpa only [← Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs] using
      frequency_coordinate_abs_le_radius k i
  calc
    _ = (frequencyRadius k : ℝ)^n*
        (‖(physicalPeriod : ℂ)*Complex.I*(k i : ℂ)‖*‖a k‖) := by rw [norm_mul]
    _ ≤ (frequencyRadius k : ℝ)^n*((physicalPeriod*(frequencyRadius k : ℝ))*‖a k‖) := by
      gcongr
    _ = physicalPeriod*((frequencyRadius k : ℝ)^(n+1)*‖a k‖) := by rw [pow_succ]; ring

/-- All ordered derivatives are actual derivatives of the convergent
 series, with a proved summable operator bound at every induction step. -/
theorem unitFourierSeries_word (a : SpatialFrequency → ℂ) (ha : FourierRapidlySummable a)
    (w : List (Fin 3)) :
    spatialWordPartial (unitFourierSeries a) w=
      unitFourierSeries (fun k => unitModeWordFactor k w*a k) := by
  induction w using List.reverseRecOn generalizing a with
  | nil => simp only [spatialWordPartial,unitModeWordFactor,List.map_nil,List.prod_nil,one_mul]
  | append_singleton w i ih =>
    rw [spatialWordPartial_append,unitFourierSeries_partial a ha i,ih _ (ha.partial i)]
    apply congrArg unitFourierSeries
    funext k
    simp only [unitModeWordFactor,List.map_append,List.prod_append,List.map_singleton,List.prod_singleton]
    ring

/-- Original `FourierRapidlySummable.word` guarantee for the `FourierSeries` construction; the complete source hypotheses are retained. -/
theorem FourierRapidlySummable.word {a : SpatialFrequency → ℂ}
    (ha : FourierRapidlySummable a) (w : List (Fin 3)) :
    FourierRapidlySummable (fun k => unitModeWordFactor k w*a k) := by
  induction w using List.reverseRecOn generalizing a with
  | nil => simpa only [unitModeWordFactor,List.map_nil,List.prod_nil,one_mul] using ha
  | append_singleton w i ih =>
    have h := ih (ha.partial i)
    convert h using 1
    funext k
    simp only [unitModeWordFactor,List.map_append,List.prod_append,List.map_singleton,List.prod_singleton]
    ring

/-- Original `unitFourierSeries_terms_summable` guarantee for the `FourierSeries` construction; the complete source hypotheses are retained. -/
theorem unitFourierSeries_terms_summable (a : SpatialFrequency → ℂ)
    (ha : FourierRapidlySummable a) (x : SpatialPoint) :
    Summable (fun k => a k*unitFourierMode k x) := by
  apply (ha 0).of_norm_bounded
  intro k
  simp only [norm_mul,unitFourierMode_norm,mul_one,pow_zero,one_mul,le_refl]

/-- Original `unitFourierSeries_finsetSum` guarantee for the `FourierSeries` construction; the complete source hypotheses are retained. -/
theorem unitFourierSeries_finsetSum {J : Type*} (a : J → SpatialFrequency → ℂ)
    (ha : ∀ j, FourierRapidlySummable (a j)) (s : Finset J) (x : SpatialPoint) :
    unitFourierSeries (fun k => ∑ j ∈ s, a j k) x=
      ∑ j ∈ s, unitFourierSeries (a j) x := by
  unfold unitFourierSeries
  simp_rw [Finset.sum_mul]
  exact Summable.tsum_finsetSum (fun j _ => unitFourierSeries_terms_summable (a j) (ha j) x)

end Qatlib.Concepts.EffectiveGauge.TorusFourier
