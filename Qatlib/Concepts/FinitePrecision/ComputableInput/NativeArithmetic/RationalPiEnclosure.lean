/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

set_option autoImplicit false
namespace Qatlib.Concepts.FinitePrecision.ComputableInput.RationalPiEnclosure
open scoped BigOperators

def atanTermQ (a n : ℕ) : ℚ :=
  (-1 : ℚ)^n/(((2*n+1 : ℕ) : ℚ)*(a : ℚ)^(2*n+1))

def atanPartialQ (a n : ℕ) : ℚ := ∑ k ∈ Finset.range n, atanTermQ a k

def atanIntervalQ (a n : ℕ) : ℚ × ℚ :=
  let p := atanPartialQ a n
  let q := p+atanTermQ a n
  (min p q, max p q)

def machinIntervalQ (n : ℕ) : ℚ × ℚ :=
  let a := atanIntervalQ 5 n
  let b := atanIntervalQ 239 n
  (16*a.1-4*b.2, 16*a.2-4*b.1)

noncomputable section
open Filter
open scoped Topology

def atanMagnitude (a n : ℕ) : ℝ := 1/(((2*n+1 : ℕ) : ℝ)*(a : ℝ)^(2*n+1))

theorem atan_term_cast (a n : ℕ) : (atanTermQ a n : ℝ)=(-1 : ℝ)^n*atanMagnitude a n := by
  simp only [atanTermQ, atanMagnitude, Rat.cast_div, Rat.cast_pow, Rat.cast_mul,
    Rat.cast_natCast, Rat.cast_neg, Rat.cast_one]
  ring

theorem atan_partial_cast (a n : ℕ) : (atanPartialQ a n : ℝ)=
    ∑ k ∈ Finset.range n, (-1 : ℝ)^k*atanMagnitude a k := by
  simp only [atanPartialQ, Rat.cast_sum, atan_term_cast]

theorem atan_partial_succ_cast (a n : ℕ) : (atanPartialQ a (n+1) : ℝ)=
    (atanPartialQ a n : ℝ)+(atanTermQ a n : ℝ) := by
  simp only [atanPartialQ, Finset.sum_range_succ, Rat.cast_add]

theorem atan_magnitude_antitone (a : ℕ) (ha : 2 ≤ a) : Antitone (atanMagnitude a) := by
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (by omega : 1 ≤ a)
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  apply antitone_nat_of_succ_le
  intro n
  unfold atanMagnitude
  apply one_div_le_one_div_of_le (by positivity)
  exact mul_le_mul (by exact_mod_cast (by omega : 2*n+1 ≤ 2*(n+1)+1))
    (pow_le_pow_right₀ ha1 (by omega : 2*n+1 ≤ 2*(n+1)+1)) (by positivity) (by positivity)

theorem atan_magnitude_hasSum (a : ℕ) (ha : 2 ≤ a) :
    HasSum (fun n : ℕ => (-1 : ℝ)^n*atanMagnitude a n) (Real.arctan (1/(a : ℝ))) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have ha1 : (1 : ℝ) < a := by exact_mod_cast (by omega : 1 < a)
  have hn : ‖(1 : ℝ)/(a : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact (div_lt_one ha0).mpr ha1
  have hterm (n : ℕ) : (-1 : ℝ)^n*(1/(a : ℝ))^(2*n+1)/((2*n+1 : ℕ) : ℝ) =
      (-1 : ℝ)^n*atanMagnitude a n := by
    have hn0 : ((2*n+1 : ℕ) : ℝ) ≠ 0 := by positivity
    unfold atanMagnitude
    rw [div_pow]
    simp only [one_pow]
    field_simp
  convert Real.hasSum_arctan hn using 1
  funext n
  exact (hterm n).symm

theorem atan_interval_contains (a n : ℕ) (ha : 2 ≤ a) :
    ((atanIntervalQ a n).1 : ℝ) ≤ Real.arctan (1/(a : ℝ)) ∧
      Real.arctan (1/(a : ℝ)) ≤ ((atanIntervalQ a n).2 : ℝ) := by
  have ht := (atan_magnitude_hasSum a ha).tendsto_sum_nat
  have hanti := atan_magnitude_antitone a ha
  have hEven (k : ℕ) : (atanPartialQ a (2*k) : ℝ) ≤ Real.arctan (1/(a : ℝ)) := by
    rw [atan_partial_cast]
    exact hanti.alternating_series_le_tendsto ht k
  have hOdd (k : ℕ) : Real.arctan (1/(a : ℝ)) ≤ (atanPartialQ a (2*k+1) : ℝ) := by
    rw [atan_partial_cast]
    exact hanti.tendsto_le_alternating_series ht k
  simp only [atanIntervalQ, Rat.cast_min, Rat.cast_max, Rat.cast_add]
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨k,rfl⟩ := even_iff_exists_two_mul.mp he
    have hu := hOdd k
    rw [atan_partial_succ_cast] at hu
    exact ⟨(min_le_left _ _).trans (hEven k), hu.trans (le_max_right _ _)⟩
  · obtain ⟨k,rfl⟩ := odd_iff_exists_bit1.mp ho
    have hl := hEven (k+1)
    rw [show 2*(k+1)=(2*k+1)+1 by omega, atan_partial_succ_cast] at hl
    exact ⟨(min_le_right _ _).trans hl, (hOdd k).trans (le_max_left _ _)⟩

theorem machin_interval_contains (n : ℕ) :
    ((machinIntervalQ n).1 : ℝ) ≤ Real.pi ∧ Real.pi ≤ ((machinIntervalQ n).2 : ℝ) := by
  have h5 := atan_interval_contains 5 n (by omega)
  have h239 := atan_interval_contains 239 n (by omega)
  have hm := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  change _ ≤ _ ∧ _ ≤ _
  simp only [machinIntervalQ, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat]
  norm_num only [one_div] at h5 h239
  constructor <;> linarith

end
end Qatlib.Concepts.FinitePrecision.ComputableInput.RationalPiEnclosure

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.RationalPiEnclosure
open scoped BigOperators

def initialPiTerms (bits : ℕ) : ℕ := max 1 ((bits+8)/4)

def piCandidateQ (bits : ℕ) : ℚ × ℚ := machinIntervalQ (initialPiTerms bits)

def piInitialIterationQ (bits : ℕ) : Option (ℚ × ℚ) :=
  let p := piCandidateQ bits
  if p.2-p.1 ≤ (1 : ℚ)/(2 : ℚ)^bits then some p else none

noncomputable section

theorem atan_interval_width (a n : ℕ) (ha : 2 ≤ a) :
    ((atanIntervalQ a n).2 : ℝ)-((atanIntervalQ a n).1 : ℝ)=atanMagnitude a n := by
  simp only [atanIntervalQ, Rat.cast_min, Rat.cast_max, Rat.cast_add]
  rw [max_sub_min_eq_abs]
  have hp : (atanPartialQ a n : ℝ)+(atanTermQ a n : ℝ)-(atanPartialQ a n : ℝ) =
      (atanTermQ a n : ℝ) := by ring
  rw [hp, atan_term_cast, abs_mul, abs_pow]
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have hm : 0 ≤ atanMagnitude a n := by unfold atanMagnitude; positivity
  simp [abs_of_nonneg hm]

theorem machin_interval_width (n : ℕ) :
    ((machinIntervalQ n).2 : ℝ)-((machinIntervalQ n).1 : ℝ) =
      16*atanMagnitude 5 n+4*atanMagnitude 239 n := by
  have h5 := atan_interval_width 5 n (by omega)
  have h239 := atan_interval_width 239 n (by omega)
  simp only [machinIntervalQ, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat]
  linarith

theorem atan_magnitude_le_five_power (a n : ℕ) (ha : 5 ≤ a) :
    atanMagnitude a n ≤ 1/(5 : ℝ)^(2*n+1) := by
  have ha5 : (5 : ℝ) ≤ a := by exact_mod_cast ha
  have ha0 : (0 : ℝ) ≤ a := by positivity
  have ho : (1 : ℝ) ≤ ((2*n+1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2*n+1)
  have hp : (5 : ℝ)^(2*n+1) ≤ (a : ℝ)^(2*n+1) := pow_le_pow_left₀ (by norm_num) ha5 _
  have hm := mul_le_mul_of_nonneg_right ho (pow_nonneg ha0 (2*n+1))
  unfold atanMagnitude
  exact one_div_le_one_div_of_le (by positivity) (hp.trans (by simpa only [one_mul] using hm))

theorem five_power_inv_le_dyadic (n : ℕ) : 1/(5 : ℝ)^(2*n+1) ≤ 1/(2 : ℝ)^(4*n+2) := by
  have hp : (4 : ℝ)^(2*n+1) ≤ (5 : ℝ)^(2*n+1) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have he : (4 : ℝ)^(2*n+1)=(2 : ℝ)^(4*n+2) := by
    rw [show (4 : ℝ)=(2 : ℝ)^2 by norm_num, ← pow_mul]
    congr 1
    omega
  rw [he] at hp
  exact one_div_le_one_div_of_le (by positivity) hp

theorem pi_candidate_width (bits : ℕ) :
    ((piCandidateQ bits).2 : ℝ)-((piCandidateQ bits).1 : ℝ) ≤
      (5/32 : ℝ)*(1/(2 : ℝ)^bits) := by
  let n := initialPiTerms bits
  have hn : 4*n ≥ bits+5 := by dsimp [n, initialPiTerms]; omega
  have h5 := atan_magnitude_le_five_power 5 n (by omega)
  have h239 := atan_magnitude_le_five_power 239 n (by omega)
  have hfirst : 16*atanMagnitude 5 n+4*atanMagnitude 239 n ≤ 20/(5 : ℝ)^(2*n+1) := by
    calc
      _ ≤ 16*(1/(5 : ℝ)^(2*n+1))+4*(1/(5 : ℝ)^(2*n+1)) := add_le_add
        (mul_le_mul_of_nonneg_left h5 (by norm_num)) (mul_le_mul_of_nonneg_left h239 (by norm_num))
      _ = _ := by ring
  have hpow : (2 : ℝ)^(bits+7) ≤ (2 : ℝ)^(4*n+2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hinv := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (2 : ℝ)^(bits+7)) hpow
  calc
    _ = 16*atanMagnitude 5 n+4*atanMagnitude 239 n := machin_interval_width n
    _ ≤ 20/(5 : ℝ)^(2*n+1) := hfirst
    _ ≤ 20/(2 : ℝ)^(4*n+2) := by
      have hh := mul_le_mul_of_nonneg_left (five_power_inv_le_dyadic n) (by norm_num : (0 : ℝ) ≤ 20)
      simpa only [mul_one_div] using hh
    _ ≤ 20/(2 : ℝ)^(bits+7) := by
      have hh := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 20)
      simpa only [mul_one_div] using hh
    _ = _ := by rw [pow_add]; norm_num; ring

theorem pi_candidate_guard (bits : ℕ) :
    (piCandidateQ bits).2-(piCandidateQ bits).1 ≤ (1 : ℚ)/(2 : ℚ)^bits := by
  have hw := pi_candidate_width bits
  have hle : (5/32 : ℝ)*(1/(2 : ℝ)^bits) ≤ 1/(2 : ℝ)^bits :=
    mul_le_of_le_one_left (by positivity) (by norm_num)
  have hr := hw.trans hle
  have hr' : (((piCandidateQ bits).2-(piCandidateQ bits).1 : ℚ) : ℝ) ≤
      (((1 : ℚ)/(2 : ℚ)^bits : ℚ) : ℝ) := by
    simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using hr
  exact Rat.cast_le.mp hr'

theorem pi_initial_iteration_returns (bits : ℕ) :
    piInitialIterationQ bits=some (piCandidateQ bits) := by
  unfold piInitialIterationQ
  rw [if_pos (pi_candidate_guard bits)]

theorem pi_candidate_valid (bits : ℕ) (hb : 1 ≤ bits) :
    (3 : ℝ) < ((piCandidateQ bits).1 : ℝ) ∧
    ((piCandidateQ bits).1 : ℝ) ≤ Real.pi ∧ Real.pi ≤ ((piCandidateQ bits).2 : ℝ) ∧
    ((piCandidateQ bits).2 : ℝ) < 4 := by
  have hc := machin_interval_contains (initialPiTerms bits)
  have hw := pi_candidate_width bits
  have hp : (2 : ℝ)^1 ≤ (2 : ℝ)^bits := pow_le_pow_right₀ (by norm_num) hb
  have hi : 1/(2 : ℝ)^bits ≤ 1/2 := by
    simpa only [pow_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < (2 : ℝ)^1) hp
  have hs : ((piCandidateQ bits).2 : ℝ)-((piCandidateQ bits).1 : ℝ) ≤ 5/64 := by nlinarith
  change ((piCandidateQ bits).1 : ℝ) ≤ Real.pi ∧ Real.pi ≤ ((piCandidateQ bits).2 : ℝ) at hc
  refine ⟨?_, hc.1, hc.2, ?_⟩ <;> linarith [Real.pi_gt_d2, Real.pi_lt_d2]

end
end Qatlib.Concepts.FinitePrecision.ComputableInput.RationalPiEnclosure
