/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.PoissonCoefficient

set_option backward.isDefEq.respectTransparency false

/-!
# Frequency Energy Tail

Torus Fourier constructions for Effective Gauge.
Defines `frequencySixthEnergy`.
Proves `frequencySixthEnergy_ge_radius`, `frequencyEnergy_le_radius`, `frequencyH1_tail_weight`.
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of frequency Sixth Energy in the Torus Fourier construction. -/
def frequencySixthEnergy (k : SpatialFrequency) : ℝ := ∑ j : Fin 3, (k j : ℝ)^6

/-- Original `frequencySixthEnergy_ge_radius` guarantee for the `FrequencyEnergyTail` construction; the complete source hypotheses are retained. -/
theorem frequencySixthEnergy_ge_radius (k : SpatialFrequency) :
    (frequencyRadius k : ℝ)^6 ≤ frequencySixthEnergy k := by
  obtain ⟨i,hi⟩ := frequencyRadius_attained k
  have habs : |(k i : ℝ)|=(frequencyRadius k : ℝ) := by
    simpa only [Nat.cast_natAbs,Int.cast_abs] using congrArg (fun n : ℕ => (n : ℝ)) hi
  calc
    _ = (k i : ℝ)^6 := by
      rw [← habs,show (6 : ℕ)=2*3 by decide,pow_mul,pow_mul,sq_abs]
    _ ≤ ∑ j : Fin 3, (k j : ℝ)^6 := Finset.single_le_sum
      (fun (j : Fin 3) _ => Even.pow_nonneg (by decide : Even (6 : ℕ)) (k j : ℝ)) (Finset.mem_univ i)

/-- Original `frequencyEnergy_le_radius` guarantee for the `FrequencyEnergyTail` construction; the complete source hypotheses are retained. -/
theorem frequencyEnergy_le_radius (k : SpatialFrequency) :
    frequencyEnergy k ≤ 3*(frequencyRadius k : ℝ)^2 := by
  have hterm (j : Fin 3) : (k j : ℝ)^2 ≤ (frequencyRadius k : ℝ)^2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (k j : ℝ)) (Nat.cast_nonneg (frequencyRadius k))).mpr
        (frequency_coordinate_abs_le_radius k j)
  calc
    _ ≤ ∑ _j : Fin 3, (frequencyRadius k : ℝ)^2 := Finset.sum_le_sum (fun j _ => hterm j)
    _ = _ := by simp

/-- H3 energy controls the H1 tail directly, avoiding a lossy individual
coefficient shell estimate. Frequencies are physical integers k. -/
theorem frequencyH1_tail_weight (N : ℕ) (k : SpatialFrequency)
    (hk : k∉Finset.Icc (-N : SpatialFrequency) N) :
    1+frequencyEnergy k ≤ 4*frequencySixthEnergy k/((N : ℝ)+1)^4 := by
  have hNrN : N+1 ≤ frequencyRadius k := by
    have hnot : ¬ frequencyRadius k ≤ N := fun h => hk ((frequency_mem_cube k N).mpr h)
    omega
  have hNr : (N : ℝ)+1 ≤ frequencyRadius k := by exact_mod_cast hNrN
  have hr1 : (1 : ℝ) ≤ frequencyRadius k := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hradSq : (1 : ℝ) ≤ (frequencyRadius k : ℝ)^2 := one_le_pow₀ hr1
  have hwe : 1+frequencyEnergy k ≤ 4*(frequencyRadius k : ℝ)^2 := by
    linarith [frequencyEnergy_le_radius k]
  have hpow : ((N : ℝ)+1)^4 ≤ (frequencyRadius k : ℝ)^4 := pow_le_pow_left₀ (by positivity) hNr 4
  have hprod := mul_le_mul hpow hwe
    (by linarith [frequencyEnergy_nonneg k] : 0 ≤ 1+frequencyEnergy k)
    (by positivity : 0 ≤ (frequencyRadius k : ℝ)^4)
  apply (le_div_iff₀ (by positivity : (0 : ℝ)<((N : ℝ)+1)^4)).mpr
  calc
    _ = ((N : ℝ)+1)^4*(1+frequencyEnergy k) := by ring
    _ ≤ (frequencyRadius k : ℝ)^4*(4*(frequencyRadius k : ℝ)^2) := hprod
    _ = 4*(frequencyRadius k : ℝ)^6 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (frequencySixthEnergy_ge_radius k) (by norm_num)

end Qatlib.Concepts.EffectiveGauge.TorusFourier
