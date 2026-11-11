/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.FourierEnergyTail
import Qatlib.Concepts.EffectiveGauge.TorusFourier.FourierResidualParseval

set_option backward.isDefEq.respectTransparency false

/-!
# Fourier Residual Energy

Torus Fourier constructions for Effective Gauge.
Defines `unitFourierH1Energy`.
Proves `unitFourierResidual_H1_hasSum`, `unitFourierResidual_H1_split`, `unitFourierResidual_H1_le`.
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Normalized complex energy corresponding to physical H1 after
multiplication by L^3. The derivative term has L^-2, not an extra L^2. -/
def unitFourierH1Energy (f : SpatialPoint → ℂ) : ℝ :=
  unitBoxEnergy f+(∑ i : Fin 3, unitBoxEnergy (spatialWordPartial f [i]))/physicalPeriod^2

/-- Original `unitFourierResidual_H1_hasSum` guarantee for the `FourierResidualEnergy` construction; the complete source hypotheses are retained. -/
theorem unitFourierResidual_H1_hasSum (f : SpatialPoint → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : IsUnitPeriodicField f) (a : SpatialFrequency → ℂ) (N : ℕ) :
    HasSum (fun k : SpatialFrequency => (1+frequencyEnergy k)*
      ‖unitFourierCoefficient f hf.continuous hp k-(if k∈Finset.Icc (-N : SpatialFrequency) N then a k else 0)‖^2)
      (unitFourierH1Energy (unitFourierResidual f a N)) := by
  let r := fun k => ‖unitFourierCoefficient f hf.continuous hp k-
    (if k∈Finset.Icc (-N : SpatialFrequency) N then a k else 0)‖^2
  have hi (i : Fin 3) : HasSum (fun k => (k i : ℝ)^2*r k)
      (unitBoxEnergy (spatialWordPartial (unitFourierResidual f a N) [i])/physicalPeriod^2) := by
    have hs := (unitFourierResidual_partial_parseval f hf hp a N i).div_const (physicalPeriod^2)
    apply HasSum.congr_fun hs
    intro k
    dsimp only [r]
    field_simp [physicalPeriod_pos.ne']
  have hgrad := hasSum_sum (s := (Finset.univ : Finset (Fin 3))) (fun i _ => hi i)
  have hs := (unitFourierResidual_parseval f hf hp a N).add hgrad
  convert hs using 1
  · funext k
    dsimp only [frequencyEnergy,r]
    rw [← Finset.sum_mul]
    ring
  · simp only [unitFourierH1Energy,unitBoxEnergy,Finset.sum_div]

/-- Original `unitFourierResidual_H1_split` guarantee for the `FourierResidualEnergy` construction; the complete source hypotheses are retained. -/
theorem unitFourierResidual_H1_split (f : SpatialPoint → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : IsUnitPeriodicField f) (a : SpatialFrequency → ℂ) (N : ℕ) :
    unitFourierH1Energy (unitFourierResidual f a N)=
      (∑ k∈Finset.Icc (-N : SpatialFrequency) N, (1+frequencyEnergy k)*
        ‖unitFourierCoefficient f hf.continuous hp k-a k‖^2)+
      unitFourierH1TailEnergy f hf.continuous hp N := by
  let inside := fun k => if k∈Finset.Icc (-N : SpatialFrequency) N then
    (1+frequencyEnergy k)*‖unitFourierCoefficient f hf.continuous hp k-a k‖^2 else 0
  have hi : HasSum inside (∑ k∈Finset.Icc (-N : SpatialFrequency) N,
      (1+frequencyEnergy k)*‖unitFourierCoefficient f hf.continuous hp k-a k‖^2) := by
    have hs : HasSum inside (∑ k∈Finset.Icc (-N : SpatialFrequency) N, inside k) :=
      hasSum_sum_of_ne_finset_zero (s := Finset.Icc (-N : SpatialFrequency) N)
        (f := inside) (fun k hk => by simp only [inside,if_neg hk])
    have hsum : (∑ k∈Finset.Icc (-N : SpatialFrequency) N, inside k)=
        ∑ k∈Finset.Icc (-N : SpatialFrequency) N,
          (1+frequencyEnergy k)*‖unitFourierCoefficient f hf.continuous hp k-a k‖^2 := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [inside,if_pos hk]
    rw [hsum] at hs
    exact hs
  have hres := unitFourierResidual_H1_hasSum f hf hp a N
  let outside := fun k : SpatialFrequency => if k∈Finset.Icc (-N : SpatialFrequency) N then 0
    else (1+frequencyEnergy k)*‖unitFourierCoefficient f hf.continuous hp k‖^2
  let total := fun k : SpatialFrequency => (1+frequencyEnergy k)*
    ‖unitFourierCoefficient f hf.continuous hp k-
      (if k∈Finset.Icc (-N : SpatialFrequency) N then a k else 0)‖^2
  have hnonneg (k : SpatialFrequency) : 0 ≤ outside k := by
    dsimp only [outside]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (by linarith [frequencyEnergy_nonneg k]) (sq_nonneg _)
  have hle (k : SpatialFrequency) : outside k ≤ total k := by
    by_cases hk : k∈Finset.Icc (-N : SpatialFrequency) N
    · simp only [outside,total,if_pos hk]
      exact mul_nonneg (by linarith [frequencyEnergy_nonneg k]) (sq_nonneg _)
    · simp only [outside,total,if_neg hk,sub_zero,le_refl]
  have ht : Summable total := hres.summable
  have ho : Summable outside := Summable.of_nonneg_of_le hnonneg hle ht
  apply hres.unique
  apply HasSum.congr_fun (hi.add ho.hasSum)
  intro k
  by_cases hk : k∈Finset.Icc (-N : SpatialFrequency) N
  · simp only [inside,outside,if_pos hk,add_zero]
  · simp only [inside,outside,if_neg hk,zero_add,sub_zero]

/-- Original `unitFourierResidual_H1_le` guarantee for the `FourierResidualEnergy` construction; the complete source hypotheses are retained. -/
theorem unitFourierResidual_H1_le (f : SpatialPoint → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : IsUnitPeriodicField f) (a : SpatialFrequency → ℂ) (N : ℕ)
    (delta M3 : ℝ) (hd : 0 ≤ delta) (hM : 0 ≤ M3)
    (ha : ∀ k∈Finset.Icc (-N : SpatialFrequency) N,
      ‖unitFourierCoefficient f hf.continuous hp k-a k‖ ≤ delta)
    (hb : ∀ i x, InUnitCube x → ‖spatialWordPartial f [i,i,i] x‖ ≤ M3) :
    unitFourierH1Energy (unitFourierResidual f a N) ≤
      ((2*N+1)^3 : ℕ)*(1+3*(N : ℝ)^2)*delta^2+
        12*M3^2/(physicalPeriod^6*((N : ℝ)+1)^4) := by
  rw [unitFourierResidual_H1_split f hf hp a N]
  apply add_le_add _ (unitFourierH1TailEnergy_le f hf hp N M3 hM hb)
  have hterm (k : SpatialFrequency) (hk : k∈Finset.Icc (-N : SpatialFrequency) N) :
      (1+frequencyEnergy k)*‖unitFourierCoefficient f hf.continuous hp k-a k‖^2 ≤
        (1+3*(N : ℝ)^2)*delta^2 := by
    have hrad : (frequencyRadius k : ℝ) ≤ N := by exact_mod_cast (frequency_mem_cube k N).mp hk
    have hsq : (frequencyRadius k : ℝ)^2 ≤ (N : ℝ)^2 :=
      (sq_le_sq₀ (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr hrad
    have he : 1+frequencyEnergy k ≤ 1+3*(N : ℝ)^2 := by linarith [frequencyEnergy_le_radius k]
    exact mul_le_mul he ((sq_le_sq₀ (norm_nonneg _) hd).mpr (ha k hk)) (sq_nonneg _)
      (by positivity)
  have hsum := Finset.sum_le_sum (fun k hk => hterm k hk)
  simpa only [Finset.sum_const,frequencyCube_card,nsmul_eq_mul,Nat.cast_pow,Nat.cast_add,
    Nat.cast_mul,Nat.cast_ofNat,mul_assoc] using hsum

end Qatlib.Concepts.EffectiveGauge.TorusFourier
