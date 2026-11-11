/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.PoissonBounds

set_option backward.isDefEq.respectTransparency false

/-!
# Poisson Truncation

Torus Fourier constructions for Effective Gauge.
Defines `unitFourierTruncation`.
Proves `unitPoissonCoefficient_tail_bound`, `unitComplexPoisson_truncation_bound`, `unitRealPoisson_truncation_bound`.
-/


set_option autoImplicit false
noncomputable section
open Finset
open scoped ContDiff Topology
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of unit Fourier Truncation in the Torus Fourier construction. -/
def unitFourierTruncation (a : SpatialFrequency → ℂ) (N : ℕ) (x : SpatialPoint) : ℂ :=
  ∑ k ∈ Finset.Icc (-N : SpatialFrequency) N, a k*unitFourierMode k x

/-- Original `unitPoissonCoefficient_tail_bound` guarantee for the `PoissonTruncation` construction; the complete source hypotheses are retained. -/
theorem unitPoissonCoefficient_tail_bound (f : Fin 3 → SpatialPoint → ℂ)
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (hp : ∀ j, IsUnitPeriodicField (f j)) (M : ℝ)
    (hb : ∀ j i x, InUnitCube x → ‖spatialWordPartial (f j) (List.replicate 6 i) x‖ ≤ M)
    (N : ℕ) (hN : 0<N) (k : SpatialFrequency) (hk : N≤frequencyRadius k) :
    ‖unitPoissonCoefficient (fun j => unitFourierCoefficient (f j) (hf j).continuous (hp j)) k‖ ≤
      (3*M/(N : ℝ)^3)*(frequencyRadius k : ℝ)^(-4 : ℝ) := by
  have hM : 0≤M := (norm_nonneg _).trans (hb 0 0 0 (by intro j; norm_num))
  have hL : 1≤physicalPeriod := by dsimp [physicalPeriod]; linarith [Real.pi_gt_three]
  have hNR : (0 : ℝ)<N := Nat.cast_pos.mpr hN
  have hkR : (N : ℝ)≤frequencyRadius k := by exact_mod_cast hk
  have hr : (0 : ℝ)<frequencyRadius k := hNR.trans_le hkR
  have hknz : k≠0 := fun h => by
    rw [(frequencyRadius_eq_zero_iff k).mpr h] at hk
    omega
  have hden : (frequencyRadius k : ℝ)^7 ≤ physicalPeriod^7*(frequencyRadius k : ℝ)^7 := by
    have h := mul_le_mul_of_nonneg_right (one_le_pow₀ hL : 1≤physicalPeriod^7)
      (show 0≤(frequencyRadius k : ℝ)^7 by positivity)
    simpa using h
  have hpower : (frequencyRadius k : ℝ)^(-4 : ℝ)=
      ((frequencyRadius k : ℝ)^(4 : ℕ))⁻¹ :=
    (Real.rpow_neg (Nat.cast_nonneg _) (4 : ℝ)).trans
      (congrArg (fun z : ℝ => z⁻¹) (Real.rpow_natCast (frequencyRadius k : ℝ) 4))
  calc
    _ ≤ 3*M/(physicalPeriod^7*(frequencyRadius k : ℝ)^7) :=
      unitPoissonCoefficient_sixthOrder_decay f hf hp M hb k hknz
    _ ≤ 3*M/(frequencyRadius k : ℝ)^7 :=
      div_le_div₀ (by positivity) le_rfl (by positivity) hden
    _ = (3*M/(frequencyRadius k : ℝ)^3)*(frequencyRadius k : ℝ)^(-4 : ℝ) := by
      rw [hpower]
      field_simp [hr.ne']
    _ ≤ (3*M/(N : ℝ)^3)*(frequencyRadius k : ℝ)^(-4 : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      exact div_le_div₀ (by positivity) le_rfl (by positivity) (pow_le_pow_left₀ hNR.le hkR 3)

/-- The exact finite cube used by the value algorithm has a certified
 uniform value tail. Its N^-3 bound suffices for the executed 400*c6 budget. -/
theorem unitComplexPoisson_truncation_bound (f : Fin 3 → SpatialPoint → ℂ)
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (hp : ∀ j, IsUnitPeriodicField (f j)) (M : ℝ)
    (hb : ∀ j i x, InUnitCube x → ‖spatialWordPartial (f j) (List.replicate 6 i) x‖ ≤ M)
    (N : ℕ) (hN : 0<N) (x : SpatialPoint) :
    let a := unitPoissonCoefficient (fun j => unitFourierCoefficient (f j) (hf j).continuous (hp j))
    ‖unitComplexPoisson f hf hp x-unitFourierTruncation a N x‖ ≤ 156*M/(N : ℝ)^3 := by
  dsimp only
  let a := unitPoissonCoefficient (fun j => unitFourierCoefficient (f j) (hf j).continuous (hp j))
  let S := Finset.Icc (-N : SpatialFrequency) N
  let t := fun k : SpatialFrequency => a k*unitFourierMode k x
  have ha : FourierRapidlySummable a := unitPoissonCoefficient_rapidlySummable _
    (fun j => unitFourierCoefficient_rapidlySummable (f j) (hf j) (hp j))
  have hM : 0≤M := (norm_nonneg _).trans (hb 0 0 0 (by intro j; norm_num))
  have hs := unitFourierSeries_terms_summable a ha x
  have hsplit := hs.sum_add_tsum_subtype_compl S
  have heq : (∑' k : SpatialFrequency, t k)-(∑ k ∈ S, t k)=∑' k : {k // k ∉ S}, t k.val := by
    linear_combination -hsplit
  have hsNorm : Summable (fun k : SpatialFrequency => ‖t k‖) := by
    simpa only [t,norm_mul,unitFourierMode_norm,mul_one,pow_zero,one_mul] using ha 0
  let B := fun k : SpatialFrequency => (3*M/(N : ℝ)^3)*(frequencyRadius k : ℝ)^(-4 : ℝ)
  have hsB : Summable B := (summable_frequencyRadius_rpow (-4) (by norm_num)).mul_left _
  change ‖(∑' k : SpatialFrequency, t k)-(∑ k ∈ S, t k)‖ ≤ _
  rw [heq]
  calc
    _ ≤ ∑' k : {k // k ∉ S}, ‖t k.val‖ := norm_tsum_le_tsum_norm (hsNorm.subtype _)
    _ ≤ ∑' k : {k // k ∉ S}, B k.val :=
      (hsNorm.subtype _).tsum_mono (hsB.subtype _) (fun k => by
        have hrad : N<frequencyRadius k.val := by
          by_contra h
          exact k.prop ((frequency_mem_cube k.val N).mpr (by omega))
        change ‖a k.val*unitFourierMode k.val x‖ ≤ _
        rw [norm_mul,unitFourierMode_norm,mul_one]
        exact unitPoissonCoefficient_tail_bound f hf hp M hb N hN k.val hrad.le)
    _ ≤ ∑' k : SpatialFrequency, B k :=
      Summable.tsum_subtype_le B {k | k ∉ S} (fun k => by dsimp only [B]; positivity) hsB
    _ = (3*M/(N : ℝ)^3)*(∑' k : SpatialFrequency, (frequencyRadius k : ℝ)^(-4 : ℝ)) := tsum_mul_left
    _ ≤ (3*M/(N : ℝ)^3)*52 :=
      mul_le_mul_of_nonneg_left (tsum_frequencyRadius_rpow_le 4 (by norm_num)) (by positivity)
    _ = 156*M/(N : ℝ)^3 := by ring

/-- Original `unitRealPoisson_truncation_bound` guarantee for the `PoissonTruncation` construction; the complete source hypotheses are retained. -/
theorem unitRealPoisson_truncation_bound (f : Fin 3 → SpatialPoint → ℂ)
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (hp : ∀ j, IsUnitPeriodicField (f j)) (M : ℝ)
    (hb : ∀ j i x, InUnitCube x → ‖spatialWordPartial (f j) (List.replicate 6 i) x‖ ≤ M)
    (N : ℕ) (hN : 0<N) (x : SpatialPoint) :
    let a := unitPoissonCoefficient (fun j => unitFourierCoefficient (f j) (hf j).continuous (hp j))
    ‖unitRealPoisson f hf hp x-Complex.reCLM (unitFourierTruncation a N x)‖ ≤
      156*M/(N : ℝ)^3 := by
  dsimp only
  change ‖Complex.reCLM (unitComplexPoisson f hf hp x)-Complex.reCLM _‖ ≤ _
  rw [← map_sub]
  exact (Complex.abs_re_le_norm _).trans (unitComplexPoisson_truncation_bound f hf hp M hb N hN x)

/-- The executed 400*c6 cubic cutoff budget leaves at least half of the
 tolerance for coefficient quadrature, trig approximation and period error. -/
theorem unitRealPoisson_truncation_cutoff (f : Fin 3 → SpatialPoint → ℂ)
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (hp : ∀ j, IsUnitPeriodicField (f j)) (M : ℝ)
    (hb : ∀ j i x, InUnitCube x → ‖spatialWordPartial (f j) (List.replicate 6 i) x‖ ≤ M)
    (N : ℕ) (hN : 0<N) (tolerance : ℝ)
    (hbudget : 400*M ≤ tolerance*(N : ℝ)^3) (x : SpatialPoint) :
    let a := unitPoissonCoefficient (fun j => unitFourierCoefficient (f j) (hf j).continuous (hp j))
    ‖unitRealPoisson f hf hp x-Complex.reCLM (unitFourierTruncation a N x)‖ ≤ tolerance/2 := by
  have hM : 0≤M := (norm_nonneg _).trans (hb 0 0 0 (by intro j; norm_num))
  apply (unitRealPoisson_truncation_bound f hf hp M hb N hN x).trans
  apply (div_le_iff₀ (pow_pos (Nat.cast_pos.mpr hN) 3)).mpr
  nlinarith

end Qatlib.Concepts.EffectiveGauge.TorusFourier
