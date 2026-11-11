/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.FourierSummability

set_option backward.isDefEq.respectTransparency false

/-!
# Lattice Sum Bound

Torus Fourier constructions for Effective Gauge.
Proves `tsum_nat_rpow_neg_two_le_two`, `tsum_frequencyRadius_rpow_le`.
-/


set_option autoImplicit false
noncomputable section
open Finset
open scoped Topology
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Original `tsum_nat_rpow_neg_two_le_two` guarantee for the `LatticeSumBound` construction; the complete source hypotheses are retained. -/
theorem tsum_nat_rpow_neg_two_le_two : (∑' n : ℕ, (n : ℝ)^(-2 : ℝ)) ≤ 2 := by
  apply Real.tsum_le_of_sum_range_le (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  intro n
  have heq : (∑ i ∈ Finset.range n, (i : ℝ)^(-2 : ℝ))=
      ∑ i ∈ Finset.Ioo 0 n, (i : ℝ)^(-2 : ℝ) := by
    symm
    apply Finset.sum_subset
    · intro i hi
      exact Finset.mem_range.mpr (Finset.mem_Ioo.mp hi).2
    · intro i hi hnot
      have hz : i=0 := by
        have hn := Finset.mem_range.mp hi
        simp only [Finset.mem_Ioo,not_and] at hnot
        omega
      subst i
      simp only [Nat.cast_zero,Real.zero_rpow (by norm_num : (-2 : ℝ)≠0)]
  rw [heq]
  have hp (i : ℕ) : (i : ℝ)^(-2 : ℝ)=((i : ℝ)^2)⁻¹ := by
    rw [Real.rpow_neg (Nat.cast_nonneg _) (2 : ℝ),Real.rpow_two]
  simp_rw [hp]
  simpa using sum_Ioo_inv_sq_le (α := ℝ) 0 n

/-- Exact shell counting gives a uniform lattice sum bound. The zero
 frequency contributes zero for these negative powers, not a hidden DC term. -/
theorem tsum_frequencyRadius_rpow_le (q : ℕ) (hq : 4≤q) :
    (∑' k : SpatialFrequency, (frequencyRadius k : ℝ)^(-(q : ℝ))) ≤ 52 := by
  have hqR : (4 : ℝ)≤q := by exact_mod_cast hq
  have hs := summable_frequencyRadius_rpow (-(q : ℝ)) (by linarith)
  let s := fun n : ℕ => ((Finset.box n : Finset SpatialFrequency) : Set SpatialFrequency)
  let e := Set.sigmaEquiv s frequencyShell_partition
  have hSigma : Summable (fun p : Σ n : ℕ, s n => (frequencyRadius p.2.val : ℝ)^(-(q : ℝ))) :=
    e.summable_iff.mpr hs
  have hterm (n : ℕ) :
      (∑' k : s n, (frequencyRadius k.val : ℝ)^(-(q : ℝ)))=
        (#(Finset.box n : Finset SpatialFrequency) : ℝ)*(n : ℝ)^(-(q : ℝ)) := by
    have heach (k : s n) : frequencyRadius k.val=n := (frequency_mem_shell k.val n).mp k.prop
    have hcard : Fintype.card (s n)=#(Finset.box n : Finset SpatialFrequency) :=
      Fintype.card_coe (Finset.box n)
    dsimp only [s] at heach ⊢
    simp only [heach,tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    rw [hcard]
  have hsplit : (∑' k : SpatialFrequency, (frequencyRadius k : ℝ)^(-(q : ℝ)))=
      ∑' n : ℕ, (#(Finset.box n : Finset SpatialFrequency) : ℝ)*(n : ℝ)^(-(q : ℝ)) := by
    rw [← e.tsum_eq (fun k : SpatialFrequency => (frequencyRadius k : ℝ)^(-(q : ℝ)))]
    change (∑' p : Σ n : ℕ, s n, (frequencyRadius p.2.val : ℝ)^(-(q : ℝ)))=_
    rw [hSigma.tsum_sigma]
    exact tsum_congr hterm
  have hbound (n : ℕ) : (#(Finset.box n : Finset SpatialFrequency) : ℝ)*(n : ℝ)^(-(q : ℝ)) ≤
      26*(n : ℝ)^(-2 : ℝ) := by
    by_cases hn : n=0
    · subst n
      simp only [Nat.cast_zero,Real.zero_rpow (by linarith : -(q : ℝ)≠0),
        Real.zero_rpow (by norm_num : (-2 : ℝ)≠0),mul_zero,le_refl]
    · have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1≤n by omega)
      have hnpos : (0 : ℝ)<n := lt_of_lt_of_le zero_lt_one hnR
      rw [frequencyShell_card n (by omega)]
      calc
        _ ≤ 26*(n : ℝ)^2*(n : ℝ)^(-(q : ℝ)) := by
          push_cast
          gcongr
          nlinarith
        _ = 26*(n : ℝ)^((2 : ℝ)-(q : ℝ)) := by
          rw [sub_eq_add_neg,Real.rpow_add hnpos,Real.rpow_two]
          ring
        _ ≤ 26*(n : ℝ)^(-2 : ℝ) := by
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hnR (by linarith))
            (by norm_num)
  rw [hsplit]
  have hsShell : Summable (fun n : ℕ =>
      (#(Finset.box n : Finset SpatialFrequency) : ℝ)*(n : ℝ)^(-(q : ℝ))) :=
    (((summable_partition (s := s) (fun k => Real.rpow_nonneg (Nat.cast_nonneg _) _)
      frequencyShell_partition).mp hs).2).congr hterm
  calc
    _ ≤ ∑' n : ℕ, 26*(n : ℝ)^(-2 : ℝ) :=
      hsShell.tsum_mono ((Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ)< -1)).mul_left 26) hbound
    _ = 26*(∑' n : ℕ, (n : ℝ)^(-2 : ℝ)) := tsum_mul_left
    _ ≤ 26*2 := mul_le_mul_of_nonneg_left tsum_nat_rpow_neg_two_le_two (by norm_num)
    _ = 52 := by norm_num

end Qatlib.Concepts.EffectiveGauge.TorusFourier
