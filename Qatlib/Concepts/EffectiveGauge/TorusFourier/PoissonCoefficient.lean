/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.FourierModeBounds

set_option backward.isDefEq.respectTransparency false

/-!
# Poisson Coefficient

Torus Fourier constructions for Effective Gauge.
Defines `frequencyEnergy`, `unitPoissonCoefficient`.
Proves `frequencyEnergy_nonneg`, `frequencyEnergy_ge_radius_sq`, `frequencyEnergy_pos`.
-/


set_option autoImplicit false
noncomputable section
open Finset
open scoped ContDiff Topology
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of frequency Energy in the Torus Fourier construction. -/
def frequencyEnergy (k : SpatialFrequency) : ℝ := ∑ j : Fin 3, (k j : ℝ)^2

/-- Original `frequencyEnergy_nonneg` guarantee for the `PoissonCoefficient` construction; the complete source hypotheses are retained. -/
theorem frequencyEnergy_nonneg (k : SpatialFrequency) : 0 ≤ frequencyEnergy k :=
  Finset.sum_nonneg (fun j _ => sq_nonneg (k j : ℝ))

/-- Original `frequencyEnergy_ge_radius_sq` guarantee for the `PoissonCoefficient` construction; the complete source hypotheses are retained. -/
theorem frequencyEnergy_ge_radius_sq (k : SpatialFrequency) :
    (frequencyRadius k : ℝ)^2 ≤ frequencyEnergy k := by
  obtain ⟨i,hi⟩ := frequencyRadius_attained k
  have habs : |(k i : ℝ)|=(frequencyRadius k : ℝ) := by
    simpa only [Nat.cast_natAbs,Int.cast_abs] using congrArg (fun n : ℕ => (n : ℝ)) hi
  calc
    _ = (k i : ℝ)^2 := by rw [← habs,sq_abs]
    _ ≤ ∑ j : Fin 3, (k j : ℝ)^2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (k j : ℝ)) (Finset.mem_univ i)

/-- Original `frequencyEnergy_pos` guarantee for the `PoissonCoefficient` construction; the complete source hypotheses are retained. -/
theorem frequencyEnergy_pos (k : SpatialFrequency) (hk : k≠0) : 0<frequencyEnergy k :=
  (sq_pos_of_pos (Nat.cast_pos.mpr (frequencyRadius_pos k hk))).trans_le
    (frequencyEnergy_ge_radius_sq k)

/-- The actual inverse-Laplacian multiplier for normalized C=L*A(Lu).
 Its denominator contains one L, rather than a physical-coordinate inverse. -/
def unitPoissonCoefficient (a : Fin 3 → SpatialFrequency → ℂ) (k : SpatialFrequency) : ℂ :=
  Complex.I*(∑ j : Fin 3, (k j : ℂ)*a j k) /
    ((physicalPeriod : ℂ)*(frequencyEnergy k : ℂ))

/-- Original `unitPoissonCoefficient_zero` guarantee for the `PoissonCoefficient` construction; the complete source hypotheses are retained. -/
theorem unitPoissonCoefficient_zero (a : Fin 3 → SpatialFrequency → ℂ) :
    unitPoissonCoefficient a 0=0 := by
  simp [unitPoissonCoefficient]

/-- The exact spectral equation has the sign of Delta chi=-div C. -/
theorem unitPoissonCoefficient_laplacian (a : Fin 3 → SpatialFrequency → ℂ)
    (k : SpatialFrequency) :
    -((physicalPeriod : ℂ)^2*(frequencyEnergy k : ℂ))*unitPoissonCoefficient a k=
      -∑ j : Fin 3, ((physicalPeriod : ℂ)*Complex.I*(k j : ℂ))*a j k := by
  by_cases hk : k=0
  · subst k
    simp [unitPoissonCoefficient_zero]
  · have hL : (physicalPeriod : ℂ)≠0 := by
      exact_mod_cast physicalPeriod_pos.ne'
    have hE : (frequencyEnergy k : ℂ)≠0 := by
      exact_mod_cast (frequencyEnergy_pos k hk).ne'
    unfold unitPoissonCoefficient
    have heq : (∑ j : Fin 3, (physicalPeriod : ℂ)*Complex.I*(k j : ℂ)*a j k)=
        (physicalPeriod : ℂ)*Complex.I*(∑ j : Fin 3, (k j : ℂ)*a j k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [heq]
    field_simp [hL,hE]

/-- Original `unitPoissonCoefficient_norm_le` guarantee for the `PoissonCoefficient` construction; the complete source hypotheses are retained. -/
theorem unitPoissonCoefficient_norm_le (a : Fin 3 → SpatialFrequency → ℂ)
    (k : SpatialFrequency) (hk : k≠0) (B : ℝ) (hb : ∀ j, ‖a j k‖ ≤ B) :
    ‖unitPoissonCoefficient a k‖ ≤ 3*B/(physicalPeriod*(frequencyRadius k : ℝ)) := by
  have hr : 0<(frequencyRadius k : ℝ) := Nat.cast_pos.mpr (frequencyRadius_pos k hk)
  have hB : 0≤B := (norm_nonneg (a 0 k)).trans (hb 0)
  have hn : ‖∑ j : Fin 3, (k j : ℂ)*a j k‖ ≤ 3*(frequencyRadius k : ℝ)*B := by
    calc
      _ ≤ ∑ j : Fin 3, ‖(k j : ℂ)*a j k‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin 3, (frequencyRadius k : ℝ)*B := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul]
        apply mul_le_mul _ (hb j) (norm_nonneg _) (Nat.cast_nonneg _)
        simpa only [← Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs] using
          frequency_coordinate_abs_le_radius k j
      _ = _ := by simp; ring
  have hn' : ‖unitPoissonCoefficient a k‖=
      ‖∑ j : Fin 3, (k j : ℂ)*a j k‖/(physicalPeriod*frequencyEnergy k) := by
    simp only [unitPoissonCoefficient,norm_div,norm_mul,Complex.norm_I,one_mul,
      Complex.norm_real,Real.norm_of_nonneg physicalPeriod_pos.le,
      Real.norm_of_nonneg (frequencyEnergy_nonneg k)]
  rw [hn']
  calc
    _ ≤ (3*(frequencyRadius k : ℝ)*B)/(physicalPeriod*(frequencyRadius k : ℝ)^2) :=
      div_le_div₀ (by positivity) hn (mul_pos physicalPeriod_pos (sq_pos_of_pos hr))
        (mul_le_mul_of_nonneg_left (frequencyEnergy_ge_radius_sq k) physicalPeriod_pos.le)
    _ = _ := by field_simp [hr.ne']

/-- Original `unitPoissonCoefficient_word_sum` guarantee for the `PoissonCoefficient` construction; the complete source hypotheses are retained. -/
theorem unitPoissonCoefficient_word_sum (a : Fin 3 → SpatialFrequency → ℂ)
    (k : SpatialFrequency) :
    (∑ j : Fin 3, unitModeWordFactor k [j,j]*unitPoissonCoefficient a k)=
      -∑ j : Fin 3, ((physicalPeriod : ℂ)*Complex.I*(k j : ℂ))*a j k := by
  have hfactor (j : Fin 3) : unitModeWordFactor k [j,j]=
      -((physicalPeriod : ℂ)^2)*(k j : ℂ)^2 := by
    simp only [unitModeWordFactor,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
    calc
      _ = (physicalPeriod : ℂ)^2*Complex.I^2*(k j : ℂ)^2 := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  have henergy : (frequencyEnergy k : ℂ)=∑ j : Fin 3, (k j : ℂ)^2 := by
    simp [frequencyEnergy]
  calc
    _ = ∑ j : Fin 3, (-((physicalPeriod : ℂ)^2)*(k j : ℂ)^2)*unitPoissonCoefficient a k := by
      simp_rw [hfactor]
    _ = -((physicalPeriod : ℂ)^2)*(∑ j : Fin 3, (k j : ℂ)^2)*unitPoissonCoefficient a k := by
      rw [← Finset.sum_mul,← Finset.mul_sum]
    _ = -((physicalPeriod : ℂ)^2*(frequencyEnergy k : ℂ))*unitPoissonCoefficient a k := by
      rw [henergy]
      ring
    _ = _ := unitPoissonCoefficient_laplacian a k

end Qatlib.Concepts.EffectiveGauge.TorusFourier
