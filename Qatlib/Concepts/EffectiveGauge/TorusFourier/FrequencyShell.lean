/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.FourierMode
import Mathlib.Data.Pi.Interval
import Mathlib.Order.Interval.Finset.Box

set_option backward.isDefEq.respectTransparency false

/-!
# Frequency Shell

Torus Fourier constructions for Effective Gauge.
Defines `frequencyRadius`.
Proves `frequencyRadius_le_iff`, `frequencyRadius_eq_zero_iff`, `frequencyRadius_pos`.
-/


set_option autoImplicit false
open Finset
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of frequency Radius in the Torus Fourier construction. -/
def frequencyRadius (k : SpatialFrequency) : ℕ := max (k 0).natAbs (max (k 1).natAbs (k 2).natAbs)

/-- Original `frequencyRadius_le_iff` guarantee for the `FrequencyShell` construction; the complete source hypotheses are retained. -/
theorem frequencyRadius_le_iff (k : SpatialFrequency) (n : ℕ) :
    frequencyRadius k ≤ n ↔ ∀ i, (k i).natAbs ≤ n := by
  constructor
  · intro h i
    fin_cases i
    · exact (le_max_left _ _).trans h
    · exact (le_max_left _ _).trans ((le_max_right _ _).trans h)
    · exact (le_max_right _ _).trans ((le_max_right _ _).trans h)
  · intro h
    exact max_le (h 0) (max_le (h 1) (h 2))

/-- Original `frequencyRadius_eq_zero_iff` guarantee for the `FrequencyShell` construction; the complete source hypotheses are retained. -/
theorem frequencyRadius_eq_zero_iff (k : SpatialFrequency) : frequencyRadius k=0 ↔ k=0 := by
  constructor
  · intro h
    have hh := (frequencyRadius_le_iff k 0).mp h.le
    funext i
    have hi : (k i).natAbs=0 := by have := hh i; omega
    exact Int.natAbs_eq_zero.mp hi
  · rintro rfl
    rfl

/-- Original `frequencyRadius_pos` guarantee for the `FrequencyShell` construction; the complete source hypotheses are retained. -/
theorem frequencyRadius_pos (k : SpatialFrequency) (hk : k≠0) : 0<frequencyRadius k := by
  have hz : frequencyRadius k≠0 := fun h => hk ((frequencyRadius_eq_zero_iff k).mp h)
  omega

/-- Original `frequencyRadius_attained` guarantee for the `FrequencyShell` construction; the complete source hypotheses are retained. -/
theorem frequencyRadius_attained (k : SpatialFrequency) : ∃ i, (k i).natAbs=frequencyRadius k := by
  by_cases h0 : max (k 1).natAbs (k 2).natAbs ≤ (k 0).natAbs
  · exact ⟨0,(max_eq_left h0).symm⟩
  · by_cases h1 : (k 2).natAbs ≤ (k 1).natAbs
    · exact ⟨1,by rw [frequencyRadius,max_eq_right (by omega),max_eq_left h1]⟩
    · exact ⟨2,by rw [frequencyRadius,max_eq_right (by omega),max_eq_right (by omega)]⟩

/-- Original `frequency_mem_cube` guarantee for the `FrequencyShell` construction; the complete source hypotheses are retained. -/
theorem frequency_mem_cube (k : SpatialFrequency) (n : ℕ) :
    k ∈ Finset.Icc (-n : SpatialFrequency) n ↔ frequencyRadius k ≤ n := by
  have habs (a : ℤ) : a.natAbs ≤ n ↔ -(n : ℤ) ≤ a ∧ a ≤ (n : ℤ) := by
    rw [← Int.ofNat_le,Int.natCast_natAbs,abs_le]
  rw [frequencyRadius_le_iff]
  simp only [Finset.mem_Icc,Pi.le_def,Pi.neg_apply,Pi.natCast_apply,habs,forall_and]

/-- Original `frequency_mem_shell` guarantee for the `FrequencyShell` construction; the complete source hypotheses are retained. -/
theorem frequency_mem_shell (k : SpatialFrequency) (n : ℕ) :
    k ∈ Finset.box n ↔ frequencyRadius k=n := by
  cases n with
  | zero => simp only [Finset.box_zero,Finset.mem_singleton,frequencyRadius_eq_zero_iff]
  | succ n =>
    rw [Finset.box_succ_eq_sdiff,Finset.mem_sdiff,frequency_mem_cube,frequency_mem_cube]
    omega

/-- Original `frequencyCube_card` guarantee for the `FrequencyShell` construction; the complete source hypotheses are retained. -/
theorem frequencyCube_card (n : ℕ) : #(Finset.Icc (-n : SpatialFrequency) n)=(2*n+1)^3 := by
  have hcard : #(Finset.Icc (-n : ℤ) n)=2*n+1 := by
    rw [Int.card_Icc]
    omega
  rw [Pi.card_Icc]
  have heach (i : Fin 3) : #(Finset.Icc ((-n : SpatialFrequency) i) ((n : SpatialFrequency) i))=2*n+1 := hcard
  simp only [heach,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

/-- Original `frequencyShell_card_succ` guarantee for the `FrequencyShell` construction; the complete source hypotheses are retained. -/
theorem frequencyShell_card_succ (n : ℕ) : #(Finset.box (n+1) : Finset SpatialFrequency)=24*(n+1)^2+2 := by
  have hsub : Finset.Icc (-n : SpatialFrequency) n ⊆ Finset.Icc (-Nat.succ n : SpatialFrequency) (Nat.succ n) := by
    apply Finset.Icc_subset_Icc
    · intro i
      change -((n+1 : ℕ) : ℤ) ≤ -(n : ℤ)
      omega
    · intro i
      change (n : ℤ) ≤ ((n+1 : ℕ) : ℤ)
      omega
  rw [Finset.box_succ_eq_sdiff,Finset.card_sdiff_of_subset hsub,frequencyCube_card,frequencyCube_card]
  have hpoly : (2*n.succ+1)^3=(2*n+1)^3+(24*(n+1)^2+2) := by
    simp only [Nat.succ_eq_add_one]
    ring
  rw [hpoly,Nat.add_sub_cancel_left]

/-- Original `frequencyShell_card` guarantee for the `FrequencyShell` construction; the complete source hypotheses are retained. -/
theorem frequencyShell_card (n : ℕ) (hn : 0<n) : #(Finset.box n : Finset SpatialFrequency)=24*n^2+2 := by
  cases n with
  | zero => omega
  | succ n => exact frequencyShell_card_succ n

/-- Original `frequencyShell_partition` guarantee for the `FrequencyShell` construction; the complete source hypotheses are retained. -/
theorem frequencyShell_partition (k : SpatialFrequency) : ∃! n, k ∈ Finset.box n := by
  use frequencyRadius k
  simp only [frequency_mem_shell,true_and,forall_eq']

end Qatlib.Concepts.EffectiveGauge.TorusFourier
