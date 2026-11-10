/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMedianStats98.MainResults.DegreeLowerBound.GridMarkov
import Qatlib.Concepts.QueryComplexity.DegreeMethod.SharpMarkovBernstein
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QMedianStats98.MainResults.DegreeLowerBound

open Qatlib.Papers.QMedianStats98.MainResults.Model
open Qatlib.Concepts.QueryComplexity.DegreeMethod

def mIndex (n lo hi : ℕ) : ℕ :=
  if |(n : ℝ) / 2 - (lo : ℝ)| ≥ |(n : ℝ) / 2 - (hi : ℝ)| then lo else hi

theorem mSelect_eq_mIndex (n lo hi : ℕ) :
    mSelect n lo hi = (mIndex n lo hi : ℝ) := by
  unfold mSelect mIndex
  split <;> rfl

theorem sourceGrid_abs_eq {n k : ℕ} (hn : 0 < n) :
    |sourceGrid n k| = (2 / (n : ℝ)) * |(k : ℝ) - (n : ℝ) / 2| := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  dsimp [sourceGrid]
  have h : 2 * (k : ℝ) / (n : ℝ) - 1 =
      (2 / (n : ℝ)) * ((k : ℝ) - (n : ℝ) / 2) := by
    field_simp
  rw [h, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / (n : ℝ))]

theorem sourceGrid_abs_le_mIndex {n lo hi : ℕ} (hn : 0 < n) :
    |sourceGrid n lo| ≤ |sourceGrid n (mIndex n lo hi)| ∧
      |sourceGrid n hi| ≤ |sourceGrid n (mIndex n lo hi)| := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h2 : (0 : ℝ) ≤ 2 / (n : ℝ) := by positivity
  unfold mIndex
  by_cases hc : |(n : ℝ) / 2 - (lo : ℝ)| ≥ |(n : ℝ) / 2 - (hi : ℝ)|
  · rw [if_pos hc]
    constructor
    · exact le_refl _
    · rw [sourceGrid_abs_eq hn, sourceGrid_abs_eq hn]
      refine mul_le_mul_of_nonneg_left ?_ h2
      rw [abs_sub_comm ((hi : ℝ)) ((n : ℝ) / 2), abs_sub_comm ((lo : ℝ)) ((n : ℝ) / 2)]
      exact hc
  · rw [if_neg hc]
    have hlt : |(n : ℝ) / 2 - (lo : ℝ)| < |(n : ℝ) / 2 - (hi : ℝ)| := lt_of_not_ge hc
    constructor
    · rw [sourceGrid_abs_eq hn, sourceGrid_abs_eq hn]
      refine mul_le_mul_of_nonneg_left ?_ h2
      rw [abs_sub_comm ((lo : ℝ)) ((n : ℝ) / 2), abs_sub_comm ((hi : ℝ)) ((n : ℝ) / 2)]
      exact le_of_lt hlt
    · exact le_refl _

theorem sourceGrid_sq_complement {n k : ℕ} (hn : 0 < n) (_hk : k ≤ n) :
    1 - (sourceGrid n k) ^ 2 =
      (4 / (n : ℝ) ^ 2) * ((k : ℝ) * ((n : ℝ) - (k : ℝ))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  dsimp [sourceGrid]
  field_simp
  ring

theorem mIndex_le {n lo hi : ℕ} (hl : lo ≤ n) (hh : hi ≤ n) : mIndex n lo hi ≤ n := by
  unfold mIndex
  split <;> assumption

theorem abs_le_max_of_mem_Ioo {a p q : ℝ} (ha : a ∈ Set.Ioo p q) :
    |a| ≤ max |p| |q| := by
  rcases lt_or_ge a 0 with h0 | h0
  · have hpa : p < a := ha.1
    have hpneg : p < 0 := lt_trans hpa h0
    have hle : -a ≤ |p| := by
      rw [abs_of_neg hpneg]
      linarith
    exact (abs_of_neg h0).trans_le (hle.trans (le_max_left _ _))
  · have haq : a < q := ha.2
    have hqpos : 0 < q := lt_of_le_of_lt h0 haq
    have hle : a ≤ |q| := by
      rw [abs_of_pos hqpos]
      linarith
    exact (abs_of_nonneg h0).trans_le (hle.trans (le_max_right _ _))

theorem exists_deriv_ge_of_gap {q : Polynomial ℝ} {u v g : ℝ}
    (huv : u < v) (hgap : g ≤ |q.eval v - q.eval u|) :
    ∃ a ∈ Set.Ioo u v, g / (v - u) ≤ |q.derivative.eval a| := by
  obtain ⟨a, ha, hder⟩ := exists_deriv_eq_slope (fun x : ℝ => q.eval x) huv
    q.continuous.continuousOn
    (fun x _ => q.differentiableAt.differentiableWithinAt)
  refine ⟨a, ha, ?_⟩
  have hdv : q.derivative.eval a = (q.eval v - q.eval u) / (v - u) := by
    rw [← (q.hasDerivAt a).deriv]
    exact hder
  rw [hdv, abs_div, abs_of_pos (sub_pos.mpr huv)]
  exact div_le_div_of_nonneg_right hgap (sub_pos.mpr huv).le

theorem source_second_term_low {n lo hi : ℕ} (hn : 0 < n)
    (hl : lo ≤ n) (hh : hi ≤ n) (hne : lo ≠ hi)
    (q : Polynomial ℝ) (d : ℕ) (hd1 : 1 ≤ d) (hdeg : q.natDegree ≤ d)
    (C : ℝ) (hC0 : 0 ≤ C) (hC2 : C ≤ 2)
    (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |q.eval x| ≤ C)
    (hlo : (2 : ℝ) / 3 ≤ q.eval (sourceGrid n lo))
    (hhi : q.eval (sourceGrid n hi) ≤ (1 : ℝ) / 3) :
    Real.sqrt ((mSelect n lo hi) * ((n : ℝ) - mSelect n lo hi)) /
        (6 * deltaL lo hi) ≤ (d : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hδpos : 0 < deltaL lo hi := by
    unfold deltaL
    exact_mod_cast Nat.dist_pos_of_ne hne
  set plo := sourceGrid n lo with hplo
  set phi := sourceGrid n hi with hphi
  have hplo_mem : plo ∈ Set.Icc (-1 : ℝ) 1 := sourceGrid_mem hn hl
  have hphi_mem : phi ∈ Set.Icc (-1 : ℝ) 1 := sourceGrid_mem hn hh
  have hplo_ne : plo ≠ phi := by
    intro h
    apply hne
    have h2 : 2 * (lo : ℝ) / (n : ℝ) - 1 = 2 * (hi : ℝ) / (n : ℝ) - 1 := by
      simpa [plo, phi, sourceGrid] using h
    have : (lo : ℝ) = (hi : ℝ) := by
      field_simp at h2
      linarith
    exact_mod_cast this

  have hkey : ∃ a, (a ∈ Set.Ioo plo phi ∨ a ∈ Set.Ioo phi plo) ∧
      (n : ℝ) / (6 * deltaL lo hi) ≤ |q.derivative.eval a| := by
    have hd : |plo - phi| = 2 * deltaL lo hi / (n : ℝ) := by
      dsimp [plo, phi, deltaL]
      exact sourceGrid_distance hn lo hi
    rcases lt_or_gt_of_ne hplo_ne with hlt | hgt
    · have hgap : (1 : ℝ) / 3 ≤ |q.eval phi - q.eval plo| := by
        have h1 : (1 : ℝ) / 3 ≤ q.eval plo - q.eval phi := by linarith [hlo, hhi]
        have h2 : q.eval plo - q.eval phi ≤ |q.eval phi - q.eval plo| := by
          rw [abs_sub_comm]
          exact le_abs_self _
        linarith
      obtain ⟨a, ha, hle⟩ := exists_deriv_ge_of_gap (q := q) hlt hgap
      refine ⟨a, Or.inl ha, ?_⟩
      have hvu : phi - plo = 2 * deltaL lo hi / (n : ℝ) := by
        have : 0 < phi - plo := sub_pos.mpr hlt
        rw [← abs_of_pos this, abs_sub_comm phi plo]
        exact hd
      have heq : (1 / 3 : ℝ) / (phi - plo) = (n : ℝ) / (6 * deltaL lo hi) := by
        rw [hvu]
        field_simp
        ring
      rwa [heq] at hle
    · have hgap : (1 : ℝ) / 3 ≤ |q.eval plo - q.eval phi| := by
        have h1 : (1 : ℝ) / 3 ≤ q.eval plo - q.eval phi := by linarith [hlo, hhi]
        have h2 : q.eval plo - q.eval phi ≤ |q.eval plo - q.eval phi| := le_abs_self _
        linarith
      obtain ⟨a, ha, hle⟩ := exists_deriv_ge_of_gap (q := q) hgt hgap
      refine ⟨a, Or.inr ha, ?_⟩
      have hvu : plo - phi = 2 * deltaL lo hi / (n : ℝ) := by
        have : 0 < plo - phi := sub_pos.mpr hgt
        rw [← abs_of_pos this]
        exact hd
      have heq : (1 / 3 : ℝ) / (plo - phi) = (n : ℝ) / (6 * deltaL lo hi) := by
        rw [hvu]
        field_simp
        ring
      rwa [heq] at hle
  obtain ⟨a, habetween, hderiv⟩ := hkey
  have haIcc : a ∈ Set.Icc (-1 : ℝ) 1 := by
    rcases habetween with h | h
    · exact ⟨by linarith [h.1, hplo_mem.1, hphi_mem.1],
             by linarith [h.2, hplo_mem.2, hphi_mem.2]⟩
    · exact ⟨by linarith [h.1, hplo_mem.1, hphi_mem.1],
             by linarith [h.2, hplo_mem.2, hphi_mem.2]⟩

  have hbern := sharpBernstein_interior d q C hd1 hdeg hC0 hb a haIcc
  have hstep : Real.sqrt (1 - a ^ 2) * ((n : ℝ) / (6 * deltaL lo hi)) ≤ 2 * (d : ℝ) := by
    have h1 : Real.sqrt (1 - a ^ 2) * ((n : ℝ) / (6 * deltaL lo hi)) ≤
        Real.sqrt (1 - a ^ 2) * |q.derivative.eval a| := by
      gcongr
    have h2 : Real.sqrt (1 - a ^ 2) * |q.derivative.eval a| ≤ (d : ℝ) * C := hbern
    have h3 : (d : ℝ) * C ≤ 2 * (d : ℝ) := by
      have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      nlinarith [hC2, hd0]
    linarith

  have hk_le : mIndex n lo hi ≤ n := mIndex_le hl hh
  have hcomp := sourceGrid_sq_complement hn hk_le
  have habs : |a| ≤ |sourceGrid n (mIndex n lo hi)| := by
    have hamax : |a| ≤ max |plo| |phi| := by
      rcases habetween with h | h
      · exact abs_le_max_of_mem_Ioo h
      · rw [max_comm]
        exact abs_le_max_of_mem_Ioo h
    refine hamax.trans (max_le ?_ ?_)
    · simpa [hplo] using (sourceGrid_abs_le_mIndex (n := n) (lo := lo) (hi := hi) hn).1
    · simpa [hphi] using (sourceGrid_abs_le_mIndex (n := n) (lo := lo) (hi := hi) hn).2
  have hsq : a ^ 2 ≤ (sourceGrid n (mIndex n lo hi)) ^ 2 := by
    have h1 : |a| ^ 2 ≤ |sourceGrid n (mIndex n lo hi)| ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg a) habs 2
    simpa only [sq_abs] using h1
  have hfactor : (4 / (n : ℝ) ^ 2) * (((mIndex n lo hi : ℝ)) *
      ((n : ℝ) - (mIndex n lo hi : ℝ))) ≤ 1 - a ^ 2 := by
    rw [← hcomp]
    linarith [hsq]

  have hfa : 0 ≤ 1 - a ^ 2 := by nlinarith [haIcc.1, haIcc.2]
  have hsqa : (1 - a ^ 2) * (n : ℝ) ^ 2 ≤ 144 * (d : ℝ) ^ 2 * (deltaL lo hi) ^ 2 := by
    have hnonneg : 0 ≤ Real.sqrt (1 - a ^ 2) * ((n : ℝ) / (6 * deltaL lo hi)) := by positivity
    have hsqle : (Real.sqrt (1 - a ^ 2) * ((n : ℝ) / (6 * deltaL lo hi))) ^ 2 ≤
        (2 * (d : ℝ)) ^ 2 := pow_le_pow_left₀ hnonneg hstep 2
    have hs1 : Real.sqrt (1 - a ^ 2) ^ 2 = 1 - a ^ 2 := Real.sq_sqrt hfa
    have hrewrite : (Real.sqrt (1 - a ^ 2) * ((n : ℝ) / (6 * deltaL lo hi))) ^ 2 =
        (1 - a ^ 2) * (n : ℝ) ^ 2 / (36 * (deltaL lo hi) ^ 2) := by
      rw [mul_pow, hs1]
      field_simp
      ring
    rw [hrewrite] at hsqle
    have h36 : (0 : ℝ) < 36 * (deltaL lo hi) ^ 2 := by positivity
    rw [div_le_iff₀ h36] at hsqle
    nlinarith [hsqle]
  have hcomb : 4 * ((mIndex n lo hi : ℝ) * ((n : ℝ) - (mIndex n lo hi : ℝ))) ≤
      144 * (d : ℝ) ^ 2 * (deltaL lo hi) ^ 2 := by
    have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    have h1 : 4 * ((mIndex n lo hi : ℝ) * ((n : ℝ) - (mIndex n lo hi : ℝ))) ≤
        (1 - a ^ 2) * (n : ℝ) ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_right hfactor hn2.le
      calc 4 * ((mIndex n lo hi : ℝ) * ((n : ℝ) - (mIndex n lo hi : ℝ)))
          = ((4 / (n : ℝ) ^ 2) *
              ((mIndex n lo hi : ℝ) * ((n : ℝ) - (mIndex n lo hi : ℝ)))) * (n : ℝ) ^ 2 := by
            field_simp
          _ ≤ (1 - a ^ 2) * (n : ℝ) ^ 2 := hmul
    linarith [h1, hsqa]
  have hkprod : (mIndex n lo hi : ℝ) * ((n : ℝ) - (mIndex n lo hi : ℝ)) ≤
      36 * (d : ℝ) ^ 2 * (deltaL lo hi) ^ 2 := by linarith [hcomb]

  rw [mSelect_eq_mIndex]
  have h6 : (0 : ℝ) ≤ 6 * deltaL lo hi * (d : ℝ) := by positivity
  have hsqrt_le : Real.sqrt ((mIndex n lo hi : ℝ) * ((n : ℝ) - (mIndex n lo hi : ℝ))) ≤
      6 * deltaL lo hi * (d : ℝ) := by
    refine (Real.sqrt_le_iff).mpr ⟨h6, ?_⟩
    rw [show (6 * deltaL lo hi * (d : ℝ)) ^ 2 =
        36 * (d : ℝ) ^ 2 * (deltaL lo hi) ^ 2 by ring]
    exact hkprod
  have h6pos : (0 : ℝ) < 6 * deltaL lo hi := by positivity
  rw [div_le_iff₀ h6pos]
  nlinarith [hsqrt_le]

end Qatlib.Papers.QMedianStats98.MainResults.DegreeLowerBound
