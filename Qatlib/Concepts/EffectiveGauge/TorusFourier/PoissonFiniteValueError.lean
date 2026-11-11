/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.PoissonTermError
import Qatlib.Concepts.EffectiveGauge.TorusFourier.PoissonTruncation

set_option backward.isDefEq.respectTransparency false

/-!
# Poisson Finite Value Error

Torus Fourier constructions for Effective Gauge.
Proves `poissonList_sum_div`, `poissonList_sum_map_eq_finset`, `poissonList_sum_error`.
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Original `poissonList_sum_div` guarantee for the `PoissonFiniteValueError` construction; the complete source hypotheses are retained. -/
theorem poissonList_sum_div (values : List ℂ) (z : ℂ) :
    values.sum/z=(values.map (fun value => value/z)).sum := by
  induction values with
  | nil => simp
  | cons a rest ih => simp only [List.sum_cons,List.map_cons,add_div,ih]

/-- Original `poissonList_sum_map_eq_finset` guarantee for the `PoissonFiniteValueError` construction; the complete source hypotheses are retained. -/
theorem poissonList_sum_map_eq_finset (frequencies : List SpatialFrequency)
    (hn : frequencies.Nodup) (f : SpatialFrequency → ℂ) :
    (frequencies.map f).sum=∑ k∈frequencies.toFinset, f k := by
  classical
  induction frequencies with
  | nil => simp
  | cons k rest ih =>
    have h := List.nodup_cons.mp hn
    simp [h.1,ih h.2]

/-- Original `poissonList_sum_error` guarantee for the `PoissonFiniteValueError` construction; the complete source hypotheses are retained. -/
theorem poissonList_sum_error {α : Type*} (records : List α) (f g : α → ℂ) (error : ℝ)
    (he : ∀ record∈records, ‖f record-g record‖ ≤ error) :
    ‖(records.map f).sum-(records.map g).sum‖ ≤ (records.length : ℝ)*error := by
  induction records with
  | nil => simp
  | cons a rest ih =>
    have hrest : ∀ record∈rest, ‖f record-g record‖ ≤ error := by
      intro record hr
      exact he record (List.mem_cons_of_mem _ hr)
    calc
      _ = ‖(f a-g a)+((rest.map f).sum-(rest.map g).sum)‖ := by
        simp only [List.map_cons,List.sum_cons]
        congr 1
        ring
      _ ≤ ‖f a-g a‖+‖(rest.map f).sum-(rest.map g).sum‖ := norm_add_le _ _
      _ ≤ error+(rest.length : ℝ)*error := add_le_add (he a (by simp)) (ih hrest)
      _ = _ := by simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; ring

/-- Every stored row has the proved error: unique signed-grid keys rule
out an unchecked duplicate row beside the existential witness. -/
theorem rationalCoefficientList_row_error (coefficients : RationalFourierCoefficientList)
    (N : ℕ) (hkeys : coefficients.map Prod.fst=sourceFrequencyGrid N)
    (a : Fin 3 → SpatialFrequency → ℂ) (E : ℝ)
    (he : ∀ k∈Finset.Icc (-N : SpatialFrequency) N, ∃ out, (k,out)∈coefficients ∧
      ∀ j, ‖a j k-rationalCircleCast (out j)‖ ≤ E)
    (record : SpatialFrequency × (Fin 3 → RationalCircleSample)) (hr : record∈coefficients) :
    ∀ j, ‖a j record.1-rationalCircleCast (record.2 j)‖ ≤ E := by
  have hn : (coefficients.map Prod.fst).Nodup := by rw [hkeys]; exact sourceFrequencyGrid_nodup N
  have hk : record.1∈sourceFrequencyGrid N := by
    rw [← hkeys]
    exact List.mem_map_of_mem hr
  have hk' : record.1∈Finset.Icc (-N : SpatialFrequency) N := by
    rw [← sourceFrequencyGrid_toFinset N]
    exact List.mem_toFinset.mpr hk
  obtain ⟨out,hout,herror⟩ := he record.1 hk'
  have heq : record=(record.1,out) := List.inj_on_of_nodup_map hn hr hout rfl
  have hs : record.2=out := congrArg Prod.snd heq
  simpa only [hs] using herror

/-- Original `rationalPoissonValuePair_error` guarantee for the `PoissonFiniteValueError` construction; the complete source hypotheses are retained. -/
theorem rationalPoissonValuePair_error (coefficients : RationalFourierCoefficientList)
    (N : ℕ) (hkeys : coefficients.map Prod.fst=sourceFrequencyGrid N)
    (a : Fin 3 → SpatialFrequency → ℂ) (B E : ℝ) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hb : ∀ k∈sourceFrequencyGrid N, ∀ j, ‖a j k‖ ≤ B)
    (he : ∀ record∈coefficients, ∀ j,
      ‖a j record.1-rationalCircleCast (record.2 j)‖ ≤ E)
    (length d : ℚ) (hd : 0<d) (hd1 : d ≤ 1) (ell : ℝ)
    (hlength : (5 : ℝ)<length) (hperiod : |(length : ℝ)-physicalPeriod| ≤ ell)
    (hbalance : 3*(N : ℝ)*ell ≤ (d : ℝ)/2) (address : Fin 3 → ℚ) :
    ‖rationalCircleCast (rationalPoissonValuePair (rationalPoissonBetaList coefficients) length d address)-
      unitFourierTruncation (unitPoissonCoefficient a) N (rationalSpatialPoint address)‖ ≤
      (finitePoissonFrequencyCount N : ℝ)*(3*E/5+3*(B+E)*(d : ℝ)/5+3*B*ell/30) := by
  let actual := fun record : SpatialFrequency × (Fin 3 → RationalCircleSample) =>
    rationalCircleCast (rationalPoissonBeta record.1 record.2)*
      rationalCircleCast (rationalFourierMode length record.1 (rationalUnitWrap address) d).value/((length : ℝ) : ℂ)
  let exactTerm := fun record : SpatialFrequency × (Fin 3 → RationalCircleSample) =>
    unitPoissonCoefficient a record.1*unitFourierMode record.1 (rationalSpatialPoint address)
  have hactual : rationalCircleCast (rationalPoissonValuePair (rationalPoissonBetaList coefficients) length d address)=
      (coefficients.map actual).sum := by
    rw [rationalPoissonValuePair_cast,poissonList_sum_div]
    simp only [rationalPoissonBetaList,List.map_map,Function.comp_def,actual]
  have hexact : (coefficients.map exactTerm).sum=
      unitFourierTruncation (unitPoissonCoefficient a) N (rationalSpatialPoint address) := by
    calc
      _ = ((coefficients.map Prod.fst).map (fun k =>
          unitPoissonCoefficient a k*unitFourierMode k (rationalSpatialPoint address))).sum := by
        simp only [List.map_map,Function.comp_def,exactTerm]
      _ = _ := by
        rw [hkeys,poissonList_sum_map_eq_finset _ (sourceFrequencyGrid_nodup N),sourceFrequencyGrid_toFinset]
        rfl
  have hterm : ∀ record∈coefficients, ‖actual record-exactTerm record‖ ≤
      3*E/5+3*(B+E)*(d : ℝ)/5+3*B*ell/30 := by
    intro record hr
    have hk : record.1∈sourceFrequencyGrid N := by
      rw [← hkeys]
      exact List.mem_map_of_mem hr
    have hbeta := complexPoissonBeta_norm_le a record.1 B (hb record.1 hk)
    have hbetaError : ‖rationalCircleCast (rationalPoissonBeta record.1 record.2)-
        complexPoissonBeta a record.1‖ ≤ 3*E := by
      rw [rationalPoissonBeta_cast,norm_sub_rev]
      exact complexPoissonBeta_sub_norm_le a (fun j _ => rationalCircleCast (record.2 j)) record.1 E (he record hr)
    have hmode := rationalFourierMode_error length record.1 (rationalUnitWrap address) d hd hd1 N
      (sourceFrequencyGrid_real_bound N record.1 hk) (rationalUnitWrap_mem address) ell hperiod
    rw [rationalUnitWrap_periodic (unitFourierMode record.1) (unitFourierMode_periodic record.1)] at hmode
    have hmodeError : ‖rationalCircleCast (rationalFourierMode length record.1 (rationalUnitWrap address) d).value-
        unitFourierMode record.1 (rationalSpatialPoint address)‖ ≤ (d : ℝ) := hmode.trans (by linarith)
    have hscale : complexPoissonBeta a record.1*unitFourierMode record.1 (rationalSpatialPoint address)/
        (physicalPeriod : ℂ)=exactTerm record := by
      have hL : (physicalPeriod : ℂ)≠0 := by exact_mod_cast physicalPeriod_pos.ne'
      dsimp only [complexPoissonBeta,exactTerm]
      field_simp [hL]
    have h := poissonTerm_approximation_error
      (complexPoissonBeta a record.1) (rationalCircleCast (rationalPoissonBeta record.1 record.2))
      (unitFourierMode record.1 (rationalSpatialPoint address))
      (rationalCircleCast (rationalFourierMode length record.1 (rationalUnitWrap address) d).value)
      B E (d : ℝ) (length : ℝ) ell hB hE (Rat.cast_pos.mpr hd).le hbeta hbetaError
      (unitFourierMode_norm _ _) hmodeError hlength hperiod
    rwa [hscale] at h
  have hlengthKeys := congrArg List.length hkeys
  simp only [List.length_map,sourceFrequencyGrid_length] at hlengthKeys
  rw [hactual,← hexact]
  simpa only [hlengthKeys,finitePoissonFrequencyCount] using
    poissonList_sum_error coefficients actual exactTerm _ hterm

end Qatlib.Concepts.EffectiveGauge.TorusFourier
