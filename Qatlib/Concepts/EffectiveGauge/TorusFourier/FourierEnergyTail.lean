/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.FourierHigherEnergy
import Qatlib.Concepts.EffectiveGauge.TorusFourier.FrequencyEnergyTail

set_option backward.isDefEq.respectTransparency false

/-!
# Fourier Energy Tail

Torus Fourier constructions for Effective Gauge.
Defines `unitBoxEnergy`, `unitFourierH1TailEnergy`.
Proves `unitBoxEnergy_le`, `unitFourierCoefficient_sixth_hasSum`, `unitFourierH1TailEnergy_le`.
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of unit Box Energy in the Torus Fourier construction. -/
def unitBoxEnergy {E : Type*} [NormedAddCommGroup E] (f : SpatialPoint → E) : ℝ :=
  ∫ u : Fin 3 → ℝ in Set.pi Set.univ (fun _ => Ioc (0 : ℝ) 1), ‖f (WithLp.toLp 2 u)‖^2

/-- Original `unitBoxEnergy_le` guarantee for the `FourierEnergyTail` construction; the complete source hypotheses are retained. -/
theorem unitBoxEnergy_le {E : Type*} [NormedAddCommGroup E] (f : SpatialPoint → E) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ x, InUnitCube x → ‖f x‖ ≤ M) : unitBoxEnergy f ≤ M^2 := by
  have hfinite : volume (Set.pi Set.univ (fun _ : Fin 3 => Ioc (0 : ℝ) 1))<⊤ := by
    rw [unitCoefficientBox_volume]
    exact ENNReal.one_lt_top
  have hbound := norm_setIntegral_le_of_norm_le_const hfinite
    (f := fun u : Fin 3 → ℝ => ‖f (WithLp.toLp 2 u)‖^2) (C := M^2) (by
      intro u hu
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      apply (sq_le_sq₀ (norm_nonneg _) hM).mpr
      apply hb
      intro i
      have hi := hu i (Set.mem_univ i)
      exact ⟨hi.1.le,hi.2⟩)
  have hnorm : ‖unitBoxEnergy f‖ ≤ M^2 := by
    simpa only [unitBoxEnergy,Measure.real,unitCoefficientBox_volume,ENNReal.toReal_one,mul_one] using hbound
  exact (le_abs_self _).trans hnorm

/-- Original `unitFourierCoefficient_sixth_hasSum` guarantee for the `FourierEnergyTail` construction; the complete source hypotheses are retained. -/
theorem unitFourierCoefficient_sixth_hasSum (f : SpatialPoint → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : IsUnitPeriodicField f) :
    HasSum (fun k : SpatialFrequency => frequencySixthEnergy k*‖unitFourierCoefficient f hf.continuous hp k‖^2)
      ((∑ i : Fin 3, unitBoxEnergy (spatialWordPartial f [i,i,i]))/physicalPeriod^6) := by
  have hi (i : Fin 3) : HasSum (fun k : SpatialFrequency => (k i : ℝ)^6*
      ‖unitFourierCoefficient f hf.continuous hp k‖^2)
      (unitBoxEnergy (spatialWordPartial f [i,i,i])/physicalPeriod^6) := by
    have hs := (unitFourierCoefficient_pure_parseval f hf hp i 3).div_const (physicalPeriod^6)
    apply HasSum.congr_fun hs
    intro k
    field_simp [physicalPeriod_pos.ne']
    ring
  have hs := hasSum_sum (s := (Finset.univ : Finset (Fin 3))) (fun i _ => hi i)
  convert hs using 1
  · funext k
    simp only [frequencySixthEnergy,Finset.sum_mul]
  · rw [Finset.sum_div]

/-- Definition of unit Fourier H1 Tail Energy in the Torus Fourier construction. -/
def unitFourierH1TailEnergy (f : SpatialPoint → ℂ) (hf : Continuous f)
    (hp : IsUnitPeriodicField f) (N : ℕ) : ℝ :=
  ∑' k : SpatialFrequency, if k∈Finset.Icc (-N : SpatialFrequency) N then 0
    else (1+frequencyEnergy k)*‖unitFourierCoefficient f hf hp k‖^2

/-- Original `unitFourierH1TailEnergy_le` guarantee for the `FourierEnergyTail` construction; the complete source hypotheses are retained. -/
theorem unitFourierH1TailEnergy_le (f : SpatialPoint → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : IsUnitPeriodicField f) (N : ℕ) (M3 : ℝ) (hM : 0 ≤ M3)
    (hb : ∀ i x, InUnitCube x → ‖spatialWordPartial f [i,i,i] x‖ ≤ M3) :
    unitFourierH1TailEnergy f hf.continuous hp N ≤
      12*M3^2/(physicalPeriod^6*((N : ℝ)+1)^4) := by
  let a := fun k => ‖unitFourierCoefficient f hf.continuous hp k‖^2
  let t := fun k => if k∈Finset.Icc (-N : SpatialFrequency) N then (0 : ℝ)
    else (1+frequencyEnergy k)*a k
  let C : ℝ := 4/((N : ℝ)+1)^4
  have hC : 0 ≤ C := by positivity
  have hnonneg (k : SpatialFrequency) : 0 ≤ t k := by
    dsimp only [t]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (by linarith [frequencyEnergy_nonneg k]) (sq_nonneg _)
  have hmajor (k : SpatialFrequency) : t k ≤ C*(frequencySixthEnergy k*a k) := by
    by_cases hk : k∈Finset.Icc (-N : SpatialFrequency) N
    · simp only [t,if_pos hk]
      have he : 0 ≤ frequencySixthEnergy k := Finset.sum_nonneg
        (fun i _ => Even.pow_nonneg (by decide : Even (6 : ℕ)) (k i : ℝ))
      exact mul_nonneg hC (mul_nonneg he (sq_nonneg _))
    · simp only [t,if_neg hk]
      have h := mul_le_mul_of_nonneg_right (frequencyH1_tail_weight N k hk) (sq_nonneg (‖unitFourierCoefficient f hf.continuous hp k‖))
      convert h using 1
      dsimp only [C,a]
      ring
  have hs := (unitFourierCoefficient_sixth_hasSum f hf hp).mul_left C
  have hts : Summable t := Summable.of_nonneg_of_le hnonneg hmajor hs.summable
  have htail : unitFourierH1TailEnergy f hf.continuous hp N ≤
      C*((∑ i : Fin 3, unitBoxEnergy (spatialWordPartial f [i,i,i]))/physicalPeriod^6) := by
    exact (hts.tsum_le_tsum hmajor hs.summable).trans_eq hs.tsum_eq
  have hsum : (∑ i : Fin 3, unitBoxEnergy (spatialWordPartial f [i,i,i])) ≤ 3*M3^2 := by
    have h := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin 3))) =>
      unitBoxEnergy_le (spatialWordPartial f [i,i,i]) M3 hM (hb i))
    simpa using h
  have hbudget := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsum
    (pow_nonneg physicalPeriod_pos.le 6)) hC
  apply htail.trans
  convert hbudget using 1
  dsimp only [C]
  field_simp [physicalPeriod_pos.ne',show (N : ℝ)+1≠0 by positivity]
  ring

end Qatlib.Concepts.EffectiveGauge.TorusFourier
