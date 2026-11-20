/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.EffectiveGauge.RationalFlow.CoefficientGridExecution
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.ProdSigma
public import Qatlib.Concepts.EffectiveGauge.TorusFourier.FrequencyShell

@[expose] public section

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

/-- Converting a natural grid index to a frequency by subtracting `N` in each coordinate and then converting back recovers the original index. -/
theorem frequencyGridIndex_leftInverse (N : ℕ) :
    Function.LeftInverse (frequencyGridIndex N) (frequencyGridValue N) := by
  intro index
  rcases index with ⟨a,b,c⟩
  simp [frequencyGridIndex,frequencyGridValue,sourceMeanIndexCoord]

/-- The list enumerating the three-dimensional radius-`N` frequency grid has length `(2*N+1)^3`. -/
theorem sourceFrequencyGrid_length (N : ℕ) : (sourceFrequencyGrid N).length=(2*N+1)^3 := by
  simp only [sourceFrequencyGrid,List.length_map,sourceMeanGrid_length]

/-- Each triple of indices in the mean grid occurs at most once. -/
theorem sourceMeanGrid_nodup (M : ℕ) : (sourceMeanGrid M).Nodup := by
  have heq : sourceMeanGrid M=(List.range M).product ((List.range M).product (List.range M)) := by
    simp only [sourceMeanGrid,List.product,List.map_flatMap,List.map_map,Function.comp_def]
  rw [heq]
  exact (List.nodup_range (n := M)).product
    ((List.nodup_range (n := M)).product (List.nodup_range (n := M)))

/-- The frequency list contains no duplicate integer triples. -/
theorem sourceFrequencyGrid_nodup (N : ℕ) : (sourceFrequencyGrid N).Nodup :=
  (sourceMeanGrid_nodup _).map (frequencyGridIndex_leftInverse N).injective

/-- A frequency occurs in the grid list exactly when each integer coordinate lies between `-N` and `N`, inclusive. -/
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

/-- The set of entries in the frequency list is the closed integer coordinate box of radius `N`. -/
theorem sourceFrequencyGrid_toFinset (N : ℕ) :
    (sourceFrequencyGrid N).toFinset=Finset.Icc (-N : SpatialFrequency) N := by
  apply Finset.ext
  intro k
  simp only [List.mem_toFinset,sourceFrequencyGrid_mem,Finset.mem_Icc]
  exact forall_and

noncomputable section

/-- Every listed frequency has real coordinate magnitudes at most the grid radius `N`. -/
theorem sourceFrequencyGrid_real_bound (N : ℕ) (k : SpatialFrequency) (hk : k∈sourceFrequencyGrid N)
    (j : Fin 3) : |(k j : ℝ)| ≤ (N : ℝ) := by
  have h := (sourceFrequencyGrid_mem N k).mp hk j
  apply abs_le.mpr
  constructor
  · exact_mod_cast h.1
  · exact_mod_cast h.2

end
end Qatlib.Concepts.EffectiveGauge.TorusFourier
