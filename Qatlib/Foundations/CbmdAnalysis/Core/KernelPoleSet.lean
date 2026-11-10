/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.KernelRegulatorZeros
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
namespace CBMD
open Metric
open scoped BigOperators

noncomputable def integerRowPoleSet (m : ℕ) : Finset ℂ := by
  classical
  exact (Finset.Icc (-(m : ℤ)) m).image (fun r : ℤ => (r : ℂ) + Complex.I)

noncomputable def integerRealPoleSet (a : ℝ) (n : ℕ) : Finset ℂ := by
  classical
  exact (Finset.Icc (-(n : ℤ)) n).image (fun k : ℤ => (((k : ℝ) / a : ℝ) : ℂ))

noncomputable def integerPoleSet (m : ℕ) (a : ℝ) (n : ℕ) : Finset ℂ := by
  classical
  exact insert (-Complex.I)
    (insert (2 * Complex.I) (integerRowPoleSet m ∪ integerRealPoleSet a n))

theorem mem_integerPoleSet_iff (m : ℕ) (a : ℝ) (n : ℕ) (z : ℂ) :
    z ∈ integerPoleSet m a n ↔ z = -Complex.I ∨ z = 2 * Complex.I ∨
      (∃ r ∈ Finset.Icc (-(m : ℤ)) m, z = (r : ℂ) + Complex.I) ∨
      ∃ k ∈ Finset.Icc (-(n : ℤ)) n, z = (((k : ℝ) / a : ℝ) : ℂ) := by
  classical
  simp only [integerPoleSet, integerRowPoleSet, integerRealPoleSet,
    Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  aesop

theorem lattice_norm_le_halfgrid_iff {a : ℝ} (ha : 0 < a) (n : ℕ) (k : ℤ) :
    ‖(((k : ℝ) / a : ℝ) : ℂ)‖ ≤ ((n : ℝ) + 1 / 2) / a ↔
      k ∈ Finset.Icc (-(n : ℤ)) n := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos ha,
    div_le_div_iff_of_pos_right ha]
  rw [Finset.mem_Icc]
  constructor
  · intro hk
    have habs : (|k| : ℝ) ≤ (n : ℝ) + 1 / 2 := by exact_mod_cast hk
    have hki : |k| ≤ (n : ℤ) := by
      by_contra hn
      have hn' : (n : ℤ) + 1 ≤ |k| := by omega
      have hnr : (n : ℝ) + 1 ≤ |(k : ℝ)| := by exact_mod_cast hn'
      linarith
    exact abs_le.mp hki
  · intro hk
    have hki : |k| ≤ (n : ℤ) := abs_le.mpr hk
    have hkr : |(k : ℝ)| ≤ (n : ℝ) := by exact_mod_cast hki
    linarith

theorem lattice_norm_lt_halfgrid {a : ℝ} (ha : 0 < a) (n : ℕ) (k : ℤ)
    (hk : k ∈ Finset.Icc (-(n : ℤ)) n) :
    ‖(((k : ℝ) / a : ℝ) : ℂ)‖ < ((n : ℝ) + 1 / 2) / a := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos ha,
    div_lt_div_iff_of_pos_right ha]
  have hi : |k| ≤ (n : ℤ) := abs_le.mpr (Finset.mem_Icc.mp hk)
  have hr : |(k : ℝ)| ≤ (n : ℝ) := by exact_mod_cast hi
  linarith

theorem integerRowPole_norm_lt (m : ℕ) (r : ℤ)
    (hr : r ∈ Finset.Icc (-(m : ℤ)) m) : ‖(r : ℂ) + Complex.I‖ < (m : ℝ) + 2 := by
  have hi : |r| ≤ (m : ℤ) := abs_le.mpr (Finset.mem_Icc.mp hr)
  have hre : |(r : ℝ)| ≤ m := by exact_mod_cast hi
  have hnorm := norm_add_le (r : ℂ) Complex.I
  simp only [Complex.norm_intCast, Complex.norm_I] at hnorm
  linarith

theorem integerPoleSet_inside (m : ℕ) {a : ℝ} (ha : 0 < a) (n : ℕ)
    (hR : (m : ℝ) + 2 < ((n : ℝ) + 1 / 2) / a) :
    ∀ z ∈ integerPoleSet m a n, z ∈ ball (0 : ℂ) (((n : ℝ) + 1 / 2) / a) := by
  intro z hz
  rw [Metric.mem_ball, dist_zero_right]
  rcases (mem_integerPoleSet_iff m a n z).mp hz with h | h | ⟨r, hr, h⟩ | ⟨k, hk, h⟩
  · subst z
    simp only [norm_neg, Complex.norm_I]
    linarith [Nat.cast_nonneg (α := ℝ) m]
  · subst z
    norm_num
    linarith [Nat.cast_nonneg (α := ℝ) m]
  · subst z
    exact (integerRowPole_norm_lt m r hr).trans hR
  · subst z
    exact lattice_norm_lt_halfgrid ha n k hk

theorem integerContourDenominator_disk_zeros (m : ℕ) {a : ℝ} (ha : 0 < a) (n : ℕ)
    (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) (((n : ℝ) + 1 / 2) / a)) :
    integerContourDenominator m a z = 0 ↔ z ∈ integerPoleSet m a n := by
  rw [integerContourDenominator_eq_zero_iff m ha z, mem_integerPoleSet_iff]
  constructor
  · rintro (h | h | ⟨r, hr, h⟩ | ⟨k, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨r, hr, h⟩))
    · refine Or.inr (Or.inr (Or.inr ⟨k, ?_, h⟩))
      apply (lattice_norm_le_halfgrid_iff ha n k).mp
      rw [← h]
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  · rintro (h | h | ⟨r, hr, h⟩ | ⟨k, _, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨r, hr, h⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨k, h⟩))

theorem integerContourDenominator_sphere_ne_zero (m : ℕ) {a : ℝ} (ha : 0 < a) (n : ℕ)
    (hR : (m : ℝ) + 2 < ((n : ℝ) + 1 / 2) / a)
    (z : ℂ) (hz : z ∈ sphere (0 : ℂ) (((n : ℝ) + 1 / 2) / a)) :
    integerContourDenominator m a z ≠ 0 := by
  intro hzero
  have hzclosed := sphere_subset_closedBall hz
  have hmem := (integerContourDenominator_disk_zeros m ha n z hzclosed).mp hzero
  have hinside := integerPoleSet_inside m ha n hR z hmem
  have hnorm : ‖z‖ = ((n : ℝ) + 1 / 2) / a := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hz
  have hlt : ‖z‖ < ((n : ℝ) + 1 / 2) / a := by
    simpa only [Metric.mem_ball, dist_zero_right] using hinside
  linarith

theorem integerRowPole_injective : Function.Injective (fun r : ℤ => (r : ℂ) + Complex.I) := by
  intro r q h
  have hr : (r : ℂ) = (q : ℂ) := add_right_cancel h
  exact_mod_cast hr

theorem integerRealPole_injective {a : ℝ} (ha : 0 < a) :
    Function.Injective (fun k : ℤ => (((k : ℝ) / a : ℝ) : ℂ)) := by
  intro k l h
  have hr := Complex.ofReal_injective h
  have hk : (k : ℝ) = (l : ℝ) := (div_left_inj' ha.ne').mp hr
  exact_mod_cast hk

private theorem integerRowPoleSet_im (m : ℕ) (z : ℂ) (hz : z ∈ integerRowPoleSet m) : z.im = 1 := by
  classical
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hz
  simp

private theorem integerRealPoleSet_im (a : ℝ) (n : ℕ) (z : ℂ)
    (hz : z ∈ integerRealPoleSet a n) : z.im = 0 := by
  classical
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hz
  simp

theorem integerPoleSet_row_real_disjoint (m : ℕ) (a : ℝ) (n : ℕ) :
    Disjoint (integerRowPoleSet m) (integerRealPoleSet a n) := by
  apply Finset.disjoint_left.mpr
  intro z hr hk
  have h1 := integerRowPoleSet_im m z hr
  have h0 := integerRealPoleSet_im a n z hk
  linarith

theorem integerPoleSet_distinguished_not_mem (m : ℕ) (a : ℝ) (n : ℕ) :
    -Complex.I ∉ integerRowPoleSet m ∪ integerRealPoleSet a n ∧
    2 * Complex.I ∉ integerRowPoleSet m ∪ integerRealPoleSet a n := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with hr | hk
    · have h1 := integerRowPoleSet_im m (-Complex.I) hr
      norm_num at h1
    · have h0 := integerRealPoleSet_im a n (-Complex.I) hk
      norm_num at h0
  · intro h
    rcases Finset.mem_union.mp h with hr | hk
    · have h1 := integerRowPoleSet_im m (2 * Complex.I) hr
      norm_num at h1
    · have h0 := integerRealPoleSet_im a n (2 * Complex.I) hk
      norm_num at h0

theorem integerPoleSet_sum {M : Type*} [AddCommMonoid M] (m : ℕ) {a : ℝ}
    (ha : 0 < a) (n : ℕ) (f : ℂ → M) :
    (∑ z ∈ integerPoleSet m a n, f z) =
      f (-Complex.I) + f (2 * Complex.I) +
        (∑ r ∈ Finset.Icc (-(m : ℤ)) m, f ((r : ℂ) + Complex.I)) +
        ∑ k ∈ Finset.Icc (-(n : ℤ)) n, f (((k : ℝ) / a : ℝ) : ℂ) := by
  classical
  have hne : -Complex.I ≠ 2 * Complex.I := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  have hnon := integerPoleSet_distinguished_not_mem m a n
  have htarget : -Complex.I ∉ insert (2 * Complex.I)
      (integerRowPoleSet m ∪ integerRealPoleSet a n) := by
    simpa only [Finset.mem_insert, not_or] using And.intro hne hnon.1
  rw [integerPoleSet, Finset.sum_insert htarget, Finset.sum_insert hnon.2,
    Finset.sum_union (integerPoleSet_row_real_disjoint m a n)]
  simp only [integerRowPoleSet, integerRealPoleSet]
  rw [Finset.sum_image (fun r _ q _ h => integerRowPole_injective h),
    Finset.sum_image (fun r _ q _ h => integerRealPole_injective ha h)]
  ac_rfl

end CBMD

end Qatlib.Foundations.CbmdAnalysis.Core
