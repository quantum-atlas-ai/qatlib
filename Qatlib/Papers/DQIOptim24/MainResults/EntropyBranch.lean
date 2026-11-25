/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.DQIOptim24.MainResults.Source.EntropyInverse
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

/-!
# The increasing binary-entropy branch

On the closed half interval the bit entropy is continuous and strictly increasing,
with endpoint values zero and one. Its sublevel-set supremum therefore agrees
with its inverse on the unit interval.
-/

set_option autoImplicit false

open Qatlib.Papers.DQIOptim24.MainResults.Source

namespace Qatlib.Papers.DQIOptim24.MainResults

/-- Entropy in bits is strictly increasing on the branch used by Eq. (227). -/
private theorem bit_entropy_strict_mono : StrictMonoOn binaryEntropy (Set.Icc 0 (1 / 2)) := by
  intro a ha b hb hab
  rw [binaryEntropy_eq_binEntropy, binaryEntropy_eq_binEntropy,
    div_lt_div_iff_of_pos_right (Real.log_pos (by norm_num))]
  have h₂ : (1 / 2 : ℝ) = 2⁻¹ := one_div 2
  exact Real.binEntropy_strictMonoOn (h₂ ▸ ha) (h₂ ▸ hb) hab

/-- The sublevel supremum defining the inverse is monotone. -/
theorem binaryEntropyInv_mono : Monotone binaryEntropyInv := by
  intro y z h
  unfold binaryEntropyInv
  have hb (t : ℝ) : BddAbove {s : ℝ | s ∈ Set.Icc 0 (1 / 2) ∧ binaryEntropy s ≤ t} :=
    ⟨1 / 2, fun _ hs => hs.1.2⟩
  by_cases hy : 0 ≤ y
  · refine csSup_le_csSup (hb z) ⟨0, ?_⟩ (fun t ht => ⟨ht.1, ht.2.trans h⟩)
    exact ⟨by norm_num, by simpa [binaryEntropy] using hy⟩
  · have he (t : ℝ) (ht : t < 0) :
        {s : ℝ | s ∈ Set.Icc 0 (1 / 2) ∧ binaryEntropy s ≤ t} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro s hs
      have hnonneg : 0 ≤ binaryEntropy s := by
        rw [binaryEntropy_eq_binEntropy]
        exact div_nonneg (Real.binEntropy_nonneg hs.1.1 (hs.1.2.trans (by norm_num)))
          (Real.log_nonneg (by norm_num))
      exact (not_lt_of_ge (hnonneg.trans hs.2)) ht
    rw [he y (lt_of_not_ge hy), Real.sSup_empty]
    by_cases hz : 0 ≤ z
    · exact le_csSup (hb z) ⟨by norm_num, by simpa [binaryEntropy] using hz⟩
    · rw [he z (lt_of_not_ge hz), Real.sSup_empty]

/-- The inverse branch in Eq. (227) is a right inverse on the unit interval. -/
theorem binaryEntropy_binaryEntropyInv {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    binaryEntropy (binaryEntropyInv y) = y := by
  have hc : Continuous binaryEntropy := by
    simpa only [funext binaryEntropy_eq_binEntropy] using
      Real.binEntropy_continuous.div_const (Real.log 2)
  have h0 : binaryEntropy 0 = 0 := by norm_num [binaryEntropy]
  have h1 : binaryEntropy (1 / 2) = 1 := by
    rw [binaryEntropy_eq_binEntropy, one_div, Real.binEntropy_two_inv,
      div_self (Real.log_pos (by norm_num)).ne']
  have hm : y ∈ Set.Icc (binaryEntropy 0) (binaryEntropy (1 / 2)) := by
    rw [h0, h1]
    exact ⟨hy0, hy1⟩
  obtain ⟨q, hq, hqy⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2)
    hc.continuousOn hm
  have heq : binaryEntropyInv y = q := by
    unfold binaryEntropyInv
    have hsub : q ∈ {s : ℝ | s ∈ Set.Icc 0 (1 / 2) ∧ binaryEntropy s ≤ y} := ⟨hq, hqy.le⟩
    refine le_antisymm (csSup_le ⟨q, hsub⟩ ?_) (le_csSup ⟨1 / 2, fun _ hs => hs.1.2⟩ hsub)
    intro s hs
    have hf := bit_entropy_strict_mono.lt_iff_lt hq hs.1
    by_contra hn
    have ht := hf.mpr (lt_of_not_ge hn)
    rw [hqy] at ht
    exact (not_lt_of_ge hs.2) ht
  rwa [heq]

end Qatlib.Papers.DQIOptim24.MainResults
