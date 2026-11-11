/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.CoefficientGridExecution
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.ProdSigma
import Qatlib.Concepts.EffectiveGauge.TorusFourier.FrequencyShell

set_option backward.isDefEq.respectTransparency false

/-!
# Frequency Grid Execution

Torus Fourier constructions for Effective Gauge.
Defines `frequencyGridValue`, `frequencyGridIndex`, `sourceFrequencyGrid`.
Proves `frequencyGridIndex_leftInverse`, `sourceFrequencyGrid_length`, `sourceMeanGrid_nodup`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of frequency Grid Value in the Torus Fourier construction. -/
def frequencyGridValue (N : ℕ) (index : SourceMeanIndex) : SpatialFrequency :=
  fun j => (sourceMeanIndexCoord index j : ℤ)-(N : ℤ)

/-- Definition of frequency Grid Index in the Torus Fourier construction. -/
def frequencyGridIndex (N : ℕ) (k : SpatialFrequency) : SourceMeanIndex :=
  ((k 0+(N : ℤ)).toNat,(k 1+(N : ℤ)).toNat,(k 2+(N : ℤ)).toNat)

/-- Definition of source Frequency Grid in the Torus Fourier construction. -/
def sourceFrequencyGrid (N : ℕ) : List SpatialFrequency :=
  (sourceMeanGrid (2*N+1)).map (frequencyGridValue N)

/-- Original `frequencyGridIndex_leftInverse` guarantee for the `FrequencyGridExecution` construction; the complete source hypotheses are retained. -/
theorem frequencyGridIndex_leftInverse (N : ℕ) :
    Function.LeftInverse (frequencyGridIndex N) (frequencyGridValue N) := by
  intro index
  rcases index with ⟨a,b,c⟩
  simp [frequencyGridIndex,frequencyGridValue,sourceMeanIndexCoord]

/-- Original `sourceFrequencyGrid_length` guarantee for the `FrequencyGridExecution` construction; the complete source hypotheses are retained. -/
theorem sourceFrequencyGrid_length (N : ℕ) : (sourceFrequencyGrid N).length=(2*N+1)^3 := by
  simp only [sourceFrequencyGrid,List.length_map,sourceMeanGrid_length]

/-- Original `sourceMeanGrid_nodup` guarantee for the `FrequencyGridExecution` construction; the complete source hypotheses are retained. -/
theorem sourceMeanGrid_nodup (M : ℕ) : (sourceMeanGrid M).Nodup := by
  have heq : sourceMeanGrid M=(List.range M).product ((List.range M).product (List.range M)) := by
    simp only [sourceMeanGrid,List.product,List.map_flatMap,List.map_map,Function.comp_def]
  rw [heq]
  exact (List.nodup_range (n := M)).product
    ((List.nodup_range (n := M)).product (List.nodup_range (n := M)))

/-- Original `sourceFrequencyGrid_nodup` guarantee for the `FrequencyGridExecution` construction; the complete source hypotheses are retained. -/
theorem sourceFrequencyGrid_nodup (N : ℕ) : (sourceFrequencyGrid N).Nodup :=
  (sourceMeanGrid_nodup _).map (frequencyGridIndex_leftInverse N).injective

/-- Original `sourceFrequencyGrid_mem` guarantee for the `FrequencyGridExecution` construction; the complete source hypotheses are retained. -/
theorem sourceFrequencyGrid_mem (N : ℕ) (k : SpatialFrequency) :
    k∈sourceFrequencyGrid N ↔ ∀ j, -(N : ℤ) ≤ k j ∧ k j ≤ (N : ℤ) := by
  constructor
  · intro h
    obtain ⟨index,hindex,rfl⟩ := List.mem_map.mp h
    have hidx := (sourceMeanGrid_mem (2*N+1) index).mp hindex
    intro j
    have hi : sourceMeanIndexCoord index j<2*N+1 := by
      fin_cases j
      · exact hidx.1
      · exact hidx.2.1
      · exact hidx.2.2
    change -(N : ℤ) ≤ (sourceMeanIndexCoord index j : ℤ)-N ∧
      (sourceMeanIndexCoord index j : ℤ)-N ≤ N
    omega
  · intro hk
    let index := frequencyGridIndex N k
    have hidx : index∈sourceMeanGrid (2*N+1) := by
      apply (sourceMeanGrid_mem _ _).mpr
      have h0 := hk 0
      have h1 := hk 1
      have h2 := hk 2
      dsimp only [index,frequencyGridIndex]
      omega
    have hval : frequencyGridValue N index=k := by
      funext j
      have h0 := hk 0
      have h1 := hk 1
      have h2 := hk 2
      fin_cases j <;> simp [frequencyGridValue,index,frequencyGridIndex,sourceMeanIndexCoord]
      all_goals omega
    exact List.mem_map.mpr ⟨index,hidx,hval⟩

/-- Original `sourceFrequencyGrid_toFinset` guarantee for the `FrequencyGridExecution` construction; the complete source hypotheses are retained. -/
theorem sourceFrequencyGrid_toFinset (N : ℕ) :
    (sourceFrequencyGrid N).toFinset=Finset.Icc (-N : SpatialFrequency) N := by
  apply Finset.ext
  intro k
  simp only [List.mem_toFinset,sourceFrequencyGrid_mem,Finset.mem_Icc]
  exact forall_and

noncomputable section

/-- Original `sourceFrequencyGrid_real_bound` guarantee for the `FrequencyGridExecution` construction; the complete source hypotheses are retained. -/
theorem sourceFrequencyGrid_real_bound (N : ℕ) (k : SpatialFrequency) (hk : k∈sourceFrequencyGrid N)
    (j : Fin 3) : |(k j : ℝ)| ≤ (N : ℝ) := by
  have h := (sourceFrequencyGrid_mem N k).mp hk j
  apply abs_le.mpr
  constructor
  · exact_mod_cast h.1
  · exact_mod_cast h.2

end
end Qatlib.Concepts.EffectiveGauge.TorusFourier
