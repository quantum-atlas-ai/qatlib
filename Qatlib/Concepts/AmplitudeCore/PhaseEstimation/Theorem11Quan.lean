/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PhaseEstimation.Theorem11Stat
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Concepts.AmplitudeCore.PhaseEstimation

open scoped BigOperators Classical

lemma bhmt_phase_estimation_theorem11_distance_round (u v : ℝ) :
    bhmt11CircleDist u v = |v - u - (round (v - u) : ℝ)| := by
  unfold bhmt11CircleDist
  apply le_antisymm
  · apply csInf_le ⟨0, by rintro a ⟨z, rfl⟩; exact abs_nonneg _⟩
    refine ⟨-round (v - u), ?_⟩
    push_cast
    congr 1
    ring
  · apply le_csInf (Set.range_nonempty _)
    rintro a ⟨z, rfl⟩
    simpa only [Int.cast_neg, sub_neg_eq_add, sub_add_eq_add_sub, add_comm v] using
      round_le (v - u) (-z)

lemma bhmt_phase_estimation_theorem11_distance_bounds (u v : ℝ) :
    0 ≤ bhmt11CircleDist u v ∧ bhmt11CircleDist u v ≤ 1 / 2 := by
  rw [bhmt_phase_estimation_theorem11_distance_round]
  exact ⟨abs_nonneg _, abs_sub_round _⟩

lemma bhmt_phase_estimation_theorem11_distance_le (u v : ℝ) (z : ℤ) :
    bhmt11CircleDist u v ≤ |(z : ℝ) + v - u| := by
  apply csInf_le ⟨0, by rintro a ⟨j, rfl⟩; exact abs_nonneg _⟩
  exact ⟨z, rfl⟩

lemma bhmt_phase_estimation_theorem11_distance_symm (u v : ℝ) :
    bhmt11CircleDist u v = bhmt11CircleDist v u := by
  have h (u v : ℝ) : bhmt11CircleDist u v ≤ bhmt11CircleDist v u := by
    rw [bhmt_phase_estimation_theorem11_distance_round v u]
    convert! bhmt_phase_estimation_theorem11_distance_le u v (round (u - v)) using 1
    rw [← abs_neg]
    congr 1
    ring
  exact le_antisymm (h u v) (h v u)

noncomputable def bhmt_phase_estimation_theorem11_expSum (M : ℕ) (t : ℝ) : ℂ :=
  ∑ y : Fin M, Complex.exp (((2 * Real.pi * t * (y.val : ℝ) : ℝ) : ℂ) * Complex.I)

lemma bhmt_phase_estimation_theorem11_conj_exp (t : ℝ) :
    star (Complex.exp ((t : ℂ) * Complex.I)) =
      Complex.exp (((-t : ℝ) : ℂ) * Complex.I) := by
  change (starRingEnd ℂ) (Complex.exp ((t : ℂ) * Complex.I)) = _
  rw [← Complex.exp_conj]
  simp

lemma bhmt_phase_estimation_theorem11_amplitude (M : ℕ) (ω : ℝ) (hM : 0 < M)
    (x : Fin M) :
    ((bhmt11QFT M).conjTranspose.mulVec (bhmt11PhaseState M ω)) x =
      (M : ℂ)⁻¹ * bhmt_phase_estimation_theorem11_expSum M (ω - x.val / M) := by
  have hs : (Real.sqrt (M : ℝ) : ℂ) * (Real.sqrt (M : ℝ) : ℂ) = (M : ℂ) := by
    norm_cast
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ M by positivity)]
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
    bhmt11QFT, bhmt11PhaseState, bhmt_phase_estimation_theorem11_expSum,
    Finset.mul_sum, star_mul, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro y _
  rw [← Complex.exp_conj]
  simp only [map_mul, map_div₀, Complex.conj_ofReal, map_ofNat, Complex.conj_I]

  calc
    _ = ((Real.sqrt (M : ℝ) : ℂ) * (Real.sqrt (M : ℝ) : ℂ))⁻¹ *
        Complex.exp (((-(2 * Real.pi * (x.val : ℝ) * y.val / M)) : ℂ) * Complex.I +
          ((2 * Real.pi * ω * (y.val : ℝ)) : ℂ) * Complex.I) := by
      rw [Complex.exp_add, mul_inv_rev]
      push_cast
      ring_nf
    _ = _ := by
      rw [hs]
      congr 2
      push_cast
      ring

lemma bhmt_phase_estimation_theorem11_mass_expSum (M : ℕ) (ω : ℝ) (hM : 0 < M)
    (x : Fin M) :
    bhmt11OutcomeMass M ω x =
      ‖bhmt_phase_estimation_theorem11_expSum M (ω - x.val / M)‖ ^ 2 / (M : ℝ) ^ 2 := by
  rw [bhmt11OutcomeMass, bhmt_phase_estimation_theorem11_amplitude M ω hM x,
    norm_mul, norm_inv, Complex.norm_natCast, mul_pow]
  simp [div_eq_mul_inv, mul_comm]

lemma bhmt_phase_estimation_theorem11_expSum_shift (M : ℕ) (t : ℝ) (j : ℤ) :
    bhmt_phase_estimation_theorem11_expSum M (t - j) =
      bhmt_phase_estimation_theorem11_expSum M t := by
  apply Finset.sum_congr rfl
  intro y _
  have he : (((2 * Real.pi * (t - j) * (y.val : ℝ) : ℝ) : ℂ) * Complex.I) =
      ((2 * Real.pi * t * (y.val : ℝ) : ℝ) : ℂ) * Complex.I +
        (-j * (y.val : ℤ) : ℤ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

lemma bhmt_phase_estimation_theorem11_expSum_abs (M : ℕ) (t : ℝ) :
    ‖bhmt_phase_estimation_theorem11_expSum M t‖ ^ 2 =
      ‖bhmt_phase_estimation_theorem11_expSum M |t|‖ ^ 2 := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht]
  rw [abs_of_neg ht]
  have he : bhmt_phase_estimation_theorem11_expSum M (-t) =
      star (bhmt_phase_estimation_theorem11_expSum M t) := by
    simp only [bhmt_phase_estimation_theorem11_expSum, star_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [bhmt_phase_estimation_theorem11_conj_exp]
    congr 2
    push_cast
    ring
  rw [he, norm_star]

lemma bhmt_phase_estimation_theorem11_expSum_geometric (M : ℕ) (t : ℝ)
    (hne : Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) ≠ 1) : bhmt_phase_estimation_theorem11_expSum M t =
      (1 - Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) ^ M) /
        (1 - Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)) := by
  calc
    _ = ∑ y : Fin M, Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) ^ y.val := by
      apply Finset.sum_congr rfl
      intro y _
      exact (zoo_amplified_qft_lemma18_exp_pow (2 * Real.pi * t) y.val).symm
    _ = _ := by
      rw [Fin.sum_univ_eq_sum_range, geom_sum_eq hne]
      have h1 : (1 : ℂ) - Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) ^ M =
          -(Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) ^ M - 1) := by ring
      have h2 : (1 : ℂ) - Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) =
          -(Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) - 1) := by ring
      rw [h1, h2, neg_div_neg_eq]

lemma bhmt_phase_estimation_theorem11_expSum_sine (M : ℕ) (t : ℝ)
    (ht : 0 < t) (ht' : t ≤ 1 / 2) :
    ‖bhmt_phase_estimation_theorem11_expSum M t‖ ^ 2 =
      Real.sin ((M : ℝ) * t * Real.pi) ^ 2 / Real.sin (t * Real.pi) ^ 2 := by
  have hsin : Real.sin (t * Real.pi) ≠ 0 := ne_of_gt
    (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos]))
  have hne : Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) ≠ 1 := by
    intro h
    have hc := zoo_amplified_qft_lemma18_chord_sq (2 * Real.pi * t)
    rw [h, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hc
    have ha : 2 * Real.pi * t / 2 = t * Real.pi := by ring
    rw [ha] at hc
    exact hsin (sq_eq_zero_iff.mp (by linarith : Real.sin (t * Real.pi) ^ 2 = 0))
  have he := bhmt_phase_estimation_theorem11_expSum_geometric M t hne
  rw [he, norm_div, div_pow, zoo_amplified_qft_lemma18_exp_pow,
    zoo_amplified_qft_lemma18_chord_sq, zoo_amplified_qft_lemma18_chord_sq]
  have h1 : 2 * Real.pi * t * (M : ℝ) / 2 = (M : ℝ) * t * Real.pi := by ring
  have h2 : 2 * Real.pi * t / 2 = t * Real.pi := by ring
  rw [h1, h2, mul_div_mul_left _ _ (by norm_num : (4 : ℝ) ≠ 0)]

lemma bhmt_phase_estimation_theorem11_spaced_tail {α : Type*} (s : Finset α)
    (f : α → ℝ) (k : ℝ) (hk : 1 < k)
    (hlo : ∀ a ∈ s, k ≤ f a)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → 1 ≤ |f a - f b|) :
    ∑ a ∈ s, 1 / f a ^ 2 ≤ 1 / (k - 1) := by
  classical
  induction s using Finset.strongInductionOn generalizing k
  rename_i s ih
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp only [Finset.sum_empty]
    positivity
  obtain ⟨a, ha, hmin⟩ := s.exists_min_image f hs
  have ha1 : 1 < f a := lt_of_lt_of_le hk (hlo a ha)
  have he : ∑ b ∈ s.erase a, 1 / f b ^ 2 ≤ 1 / f a := by
    have hh := ih (s.erase a) (Finset.erase_ssubset ha) (f a + 1) (by linarith)
      (fun b hb => by
        have hb' := Finset.mem_erase.mp hb
        have hm := hmin b hb'.2
        have hd := hsep a ha b hb'.2 (Ne.symm hb'.1)
        rw [abs_of_nonpos (sub_nonpos.mpr hm)] at hd
        linarith)
      (fun b hb c hc hbc => hsep b (Finset.mem_of_mem_erase hb)
        c (Finset.mem_of_mem_erase hc) hbc)
    simpa using hh
  rw [← Finset.add_sum_erase _ _ ha]
  calc
    1 / f a ^ 2 + ∑ b ∈ s.erase a, 1 / f b ^ 2 ≤
        1 / f a ^ 2 + 1 / f a := by linarith
    _ ≤ 1 / (f a - 1) := by
      have h0 : 0 < f a := by linarith
      apply (le_div_iff₀ (by linarith : 0 < f a - 1)).mpr
      field_simp
      nlinarith
    _ ≤ 1 / (k - 1) := one_div_le_one_div_of_le (by linarith) (by linarith [hlo a ha])

lemma bhmt_phase_estimation_theorem11_scalar_endpoint (t : ℝ)
    (ht : 0 < t) (ht' : t ≤ 1 / 5) :
    8 * t ^ 2 * (1 - t) ^ 2 ≤
      Real.sin (Real.pi * t) ^ 2 * (t ^ 2 + (1 - t) ^ 2) := by
  have hp0 := Real.pi_pos
  have hpU : Real.pi ^ 2 ≤ 10 := by nlinarith [Real.pi_lt_d2]
  have hpL : 49 / 5 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_d2]
  have ht2 : t ^ 2 ≤ 1 / 25 := by nlinarith
  have hpt : 0 < Real.pi * t := mul_pos hp0 ht
  have hpt1 : Real.pi * t ≤ 1 := by nlinarith [Real.pi_lt_d2]
  have hc : (Real.pi * t) ^ 2 ≤ 10 * t ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hpU (sq_nonneg t)]
  have hs : Real.pi * t * (1 - 5 / 2 * t ^ 2) ≤ Real.sin (Real.pi * t) := by
    have : Real.pi * t - (Real.pi * t) ^ 3 / 4 < Real.sin (Real.pi * t) := by
      linarith [Real.sin_gt_sub_cube hpt, pow_nonneg hpt.le 3]
    nlinarith [mul_le_mul_of_nonneg_left hc hpt.le]
  have ha : 0 ≤ 1 - 5 / 2 * t ^ 2 := by nlinarith
  have hsq : (Real.pi * t * (1 - 5 / 2 * t ^ 2)) ^ 2 ≤
      Real.sin (Real.pi * t) ^ 2 := pow_le_pow_left₀ (mul_nonneg hpt.le ha) hs 2
  have hq : (1 - t) ^ 2 * (1 + t ^ 2) ≤ t ^ 2 + (1 - t) ^ 2 := by
    have hb : (1 - t) ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hb)]
  have hpoly : 1 - 4 * t ^ 2 ≤ (1 - 5 / 2 * t ^ 2) ^ 2 * (1 + t ^ 2) := by
    nlinarith [sq_nonneg (t ^ 2), pow_nonneg ht.le 6]
  have hnum : 8 ≤ Real.pi ^ 2 * (1 - 4 * t ^ 2) := by
    have hb : 21 / 25 ≤ 1 - 4 * t ^ 2 := by linarith
    nlinarith [mul_le_mul hpL hb (by norm_num : (0 : ℝ) ≤ 21 / 25) (sq_nonneg Real.pi)]
  calc
    8 * t ^ 2 * (1 - t) ^ 2 ≤
        t ^ 2 * (1 - t) ^ 2 * (Real.pi ^ 2 * (1 - 4 * t ^ 2)) := by
      nlinarith [mul_le_mul_of_nonneg_left hnum (show 0 ≤ t ^ 2 * (1-t)^2 by positivity)]
    _ ≤ t ^ 2 * (1 - t) ^ 2 *
        (Real.pi ^ 2 * ((1 - 5 / 2 * t ^ 2) ^ 2 * (1 + t ^ 2))) := by gcongr
    _ = (Real.pi * t * (1 - 5 / 2 * t ^ 2)) ^ 2 *
        ((1 - t) ^ 2 * (1 + t ^ 2)) := by ring
    _ ≤ (Real.pi * t * (1 - 5 / 2 * t ^ 2)) ^ 2 *
        (t ^ 2 + (1 - t) ^ 2) := by gcongr
    _ ≤ Real.sin (Real.pi * t) ^ 2 * (t ^ 2 + (1 - t) ^ 2) := by gcongr

lemma bhmt_phase_estimation_theorem11_scalar_middle (t : ℝ)
    (ht : 1 / 5 ≤ t) (ht' : t ≤ 4 / 5) :
    8 * t ^ 2 * (1 - t) ^ 2 ≤
      Real.sin (Real.pi * t) ^ 2 * (t ^ 2 + (1 - t) ^ 2) := by
  let s := 2 * t - 1
  have hs : s ^ 2 ≤ 9 / 25 := by dsimp [s]; nlinarith
  have hpU : Real.pi ^ 2 ≤ 10 := by nlinarith [Real.pi_pos, Real.pi_lt_d2]
  have hc : 1 - 5 / 4 * s ^ 2 ≤ Real.cos (Real.pi * s / 2) := by
    have := Real.one_sub_sq_div_two_le_cos (x := Real.pi * s / 2)
    nlinarith [mul_le_mul_of_nonneg_right hpU (sq_nonneg s)]
  have ha : 0 ≤ 1 - 5 / 4 * s ^ 2 := by nlinarith
  have hsq := pow_le_pow_left₀ ha hc 2
  have hpoly : (1 - s ^ 2) ^ 2 ≤ (1 + s ^ 2) * (1 - 5 / 4 * s ^ 2) ^ 2 := by
    have h1 : 0 ≤ (9 / 25 - s ^ 2) * (22 - 25 * s ^ 2) := by
      apply mul_nonneg <;> nlinarith
    have h2 := mul_nonneg (sq_nonneg s) (show 0 ≤ 2 / 25 +
        (9 / 25 - s ^ 2) * (22 - 25 * s ^ 2) by linarith)
    nlinarith
  have hfinal : (1 - s ^ 2) ^ 2 ≤ (1 + s ^ 2) * Real.cos (Real.pi * s / 2) ^ 2 := by
    exact hpoly.trans (mul_le_mul_of_nonneg_left hsq (by positivity))
  have he : Real.sin (Real.pi * t) = Real.cos (Real.pi * s / 2) := by
    rw [show Real.pi * t = Real.pi * s / 2 + Real.pi / 2 by dsimp [s]; ring,
      Real.sin_add_pi_div_two]
  rw [he]
  dsimp [s] at hfinal ⊢
  nlinarith

lemma bhmt_phase_estimation_theorem11_scalar (t : ℝ) (ht : 0 < t) (ht' : t < 1) :
    8 * t ^ 2 * (1 - t) ^ 2 ≤
      Real.sin (Real.pi * t) ^ 2 * (t ^ 2 + (1 - t) ^ 2) := by
  by_cases h1 : t ≤ 1 / 5
  · exact bhmt_phase_estimation_theorem11_scalar_endpoint t ht h1
  by_cases h2 : t ≤ 4 / 5
  · exact bhmt_phase_estimation_theorem11_scalar_middle t (by linarith) h2
  have h := bhmt_phase_estimation_theorem11_scalar_endpoint (1 - t) (by linarith) (by linarith)
  rw [show Real.pi * (1 - t) = Real.pi - Real.pi * t by ring, Real.sin_pi_sub] at h
  nlinarith

lemma bhmt_phase_estimation_theorem11_integral_of_distance_zero
    (M : ℕ) (ω : ℝ) (hM : 0 < M) (x : Fin M)
    (h : bhmt11CircleDist ω (x.val / (M : ℝ)) = 0) :
    ∃ j : ℤ, (M : ℝ) * ω = (j : ℝ) := by
  have hm : (M : ℝ) ≠ 0 := by positivity
  rw [bhmt_phase_estimation_theorem11_distance_symm,
    bhmt_phase_estimation_theorem11_distance_round, abs_eq_zero] at h
  refine ⟨(M : ℤ) * round (ω - x.val / (M : ℝ)) + x.val, ?_⟩
  push_cast
  have hh := congrArg (fun r : ℝ => r * M) h
  simp only [sub_mul, div_mul_cancel₀ _ hm, zero_mul] at hh
  nlinarith

lemma bhmt_phase_estimation_theorem11_expSum_distance (M : ℕ) (u v : ℝ) :
    ‖bhmt_phase_estimation_theorem11_expSum M (v - u)‖ ^ 2 =
      ‖bhmt_phase_estimation_theorem11_expSum M (bhmt11CircleDist u v)‖ ^ 2 := by
  rw [bhmt_phase_estimation_theorem11_distance_round,
    ← bhmt_phase_estimation_theorem11_expSum_shift M (v - u) (round (v - u))]
  exact bhmt_phase_estimation_theorem11_expSum_abs M _

lemma bhmt_phase_estimation_theorem11_mass_formula (M : ℕ) (ω : ℝ) (hM : 0 < M)
    (x : Fin M) (hd : 0 < bhmt11CircleDist ω (x.val / (M : ℝ))) :
    bhmt11OutcomeMass M ω x =
      Real.sin ((M : ℝ) * bhmt11CircleDist ω (x.val / (M : ℝ)) * Real.pi) ^ 2 /
        ((M : ℝ) ^ 2 * Real.sin (bhmt11CircleDist ω (x.val / (M : ℝ)) * Real.pi) ^ 2) := by
  rw [bhmt_phase_estimation_theorem11_mass_expSum M ω hM x,
    bhmt_phase_estimation_theorem11_expSum_distance,
    bhmt_phase_estimation_theorem11_distance_symm (x.val / (M : ℝ)) ω,
    bhmt_phase_estimation_theorem11_expSum_sine M _ hd
      (bhmt_phase_estimation_theorem11_distance_bounds _ _).2]
  ring

lemma bhmt_phase_estimation_theorem11_mass_bound (M : ℕ) (ω : ℝ) (hM : 0 < M)
    (x : Fin M) (hd : 0 < bhmt11CircleDist ω (x.val / (M : ℝ))) :
    bhmt11OutcomeMass M ω x ≤
      1 / (2 * (M : ℝ) * bhmt11CircleDist ω (x.val / (M : ℝ))) ^ 2 := by
  let d := bhmt11CircleDist ω (x.val / (M : ℝ))
  have hdp : 0 < d := hd
  have hdU : d ≤ 1 / 2 := (bhmt_phase_estimation_theorem11_distance_bounds _ _).2
  have hs : 2 * d ≤ Real.sin (d * Real.pi) := by
    have h := Real.mul_le_sin (x := d * Real.pi) (by positivity)
      (by nlinarith [Real.pi_pos])
    have he : 2 / Real.pi * (d * Real.pi) = 2 * d := by field_simp
    rwa [he] at h
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * d) hs 2
  have hden : (2 * (M : ℝ) * d) ^ 2 ≤ (M : ℝ) ^ 2 * Real.sin (d * Real.pi) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg (M : ℝ))]
  rw [bhmt_phase_estimation_theorem11_mass_formula M ω hM x hd]
  exact div_le_div₀ (by norm_num : (0 : ℝ) ≤ 1) (Real.sin_sq_le_one _) (by positivity) hden

lemma bhmt_phase_estimation_theorem11_mass_nonneg (M : ℕ) (ω : ℝ) (x : Fin M) :
    0 ≤ bhmt11OutcomeMass M ω x := sq_nonneg _

lemma bhmt_phase_estimation_theorem11_expSum_zero (M : ℕ) :
    bhmt_phase_estimation_theorem11_expSum M 0 = M := by
  simp [bhmt_phase_estimation_theorem11_expSum]

lemma bhmt_phase_estimation_theorem11_expSum_grid (M : ℕ) (hM : 0 < M) (j : ℤ)
    (hj : ¬ (M : ℤ) ∣ j) :
    bhmt_phase_estimation_theorem11_expSum M ((j : ℝ) / M) = 0 := by
  have hm : (M : ℝ) ≠ 0 := by positivity
  have hne : Complex.exp (((2 * Real.pi * ((j : ℝ) / M) : ℝ) : ℂ) * Complex.I) ≠ 1 := by
    intro h
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
    have hi := congrArg Complex.im hn
    simp at hi
    have he : (j : ℝ) / M = (n : ℝ) := by nlinarith [Real.pi_pos]
    have he' : (j : ℝ) = (n : ℝ) * M := (div_eq_iff hm).mp he
    apply hj
    refine ⟨n, ?_⟩
    exact_mod_cast (by linarith : (j : ℝ) = (M : ℝ) * n)
  rw [bhmt_phase_estimation_theorem11_expSum_geometric M _ hne,
    zoo_amplified_qft_lemma18_exp_pow]
  have he : (((2 * Real.pi * ((j : ℝ) / M) * M : ℝ) : ℂ) * Complex.I) =
      (j : ℂ) * (2 * Real.pi * Complex.I) := by
    have hmc : (M : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hM
    push_cast
    field_simp [hmc]
  rw [he, Complex.exp_int_mul_two_pi_mul_I, sub_self, zero_div]

lemma bhmt_phase_estimation_theorem11_column (M : ℕ) (x y : Fin M) :
    bhmt11QFT M y x = bhmt11PhaseState M (x.val / (M : ℝ)) y := by
  unfold bhmt11QFT bhmt11PhaseState
  congr 2
  push_cast
  ring

lemma bhmt_phase_estimation_theorem11_qft_symm (M : ℕ) (x y : Fin M) :
    bhmt11QFT M x y = bhmt11QFT M y x := by
  unfold bhmt11QFT
  congr 2
  ring

lemma bhmt_phase_estimation_theorem11_unitary (M : ℕ) (hM : 0 < M) :
    bhmt11QFT M * (bhmt11QFT M).conjTranspose = 1 := by
  ext x y
  have he : (bhmt11QFT M * (bhmt11QFT M).conjTranspose) x y =
      ((bhmt11QFT M).conjTranspose.mulVec (bhmt11PhaseState M (x.val / (M : ℝ)))) y := by
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]
    apply Finset.sum_congr rfl
    intro z _
    rw [bhmt_phase_estimation_theorem11_qft_symm M x z,
      bhmt_phase_estimation_theorem11_column M x z,
      bhmt_phase_estimation_theorem11_qft_symm M y z]
    ring
  rw [he, bhmt_phase_estimation_theorem11_amplitude M _ hM y]
  by_cases hxy : x = y
  · subst y
    simp [bhmt_phase_estimation_theorem11_expSum_zero, ne_of_gt hM]
  · have hdiv : ¬ (M : ℤ) ∣ (x.val : ℤ) - y.val := by
      intro h
      have he := (Int.emod_eq_emod_iff_emod_sub_eq_zero).mpr (Int.emod_eq_zero_of_dvd h)
      have hx : (x.val : ℤ) % M = x.val :=
          Int.emod_eq_of_lt (by positivity) (by exact_mod_cast x.isLt)
      have hy : (y.val : ℤ) % M = y.val :=
          Int.emod_eq_of_lt (by positivity) (by exact_mod_cast y.isLt)
      rw [hx, hy] at he
      exact hxy (Fin.ext (by exact_mod_cast he))
    have ht : (x.val : ℝ) / M - y.val / M = (((x.val : ℤ) - y.val : ℤ) : ℝ) / M := by
      push_cast
      ring
    rw [ht, bhmt_phase_estimation_theorem11_expSum_grid M hM _ hdiv]
    simp [hxy]

lemma bhmt_phase_estimation_theorem11_sum_norm (M : ℕ) (v : Fin M → ℂ) :
    ((∑ x, ‖v x‖ ^ 2 : ℝ) : ℂ) = star v ⬝ᵥ v := by
  simp only [dotProduct, ← Complex.normSq_eq_norm_sq, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro x _
  exact Complex.normSq_eq_conj_mul_self

lemma bhmt_phase_estimation_theorem11_state_normalized (M : ℕ) (ω : ℝ) (hM : 0 < M) :
    ∑ y : Fin M, ‖bhmt11PhaseState M ω y‖ ^ 2 = 1 := by
  have hn (y : Fin M) : ‖bhmt11PhaseState M ω y‖ ^ 2 = 1 / (M : ℝ) := by
    have he : bhmt11PhaseState M ω y = (Real.sqrt (M : ℝ) : ℂ)⁻¹ *
        Complex.exp (((2 * Real.pi * ω * (y.val : ℝ) : ℝ) : ℂ) * Complex.I) := by
      unfold bhmt11PhaseState
      push_cast
      rfl
    rw [he, norm_mul, norm_inv, Complex.norm_exp_ofReal_mul_I, mul_one,
      inv_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ M)]
    simp only [one_div]
  simp_rw [hn]
  simp [ne_of_gt hM]

lemma bhmt_phase_estimation_theorem11_normalization (M : ℕ) (ω : ℝ) (hM : 0 < M) :
    ∑ x : Fin M, bhmt11OutcomeMass M ω x = 1 := by
  have he : star ((bhmt11QFT M).conjTranspose.mulVec (bhmt11PhaseState M ω)) ⬝ᵥ
      ((bhmt11QFT M).conjTranspose.mulVec (bhmt11PhaseState M ω)) =
        star (bhmt11PhaseState M ω) ⬝ᵥ bhmt11PhaseState M ω := by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose,
      Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      bhmt_phase_estimation_theorem11_unitary M hM, Matrix.vecMul_one]
  rw [← bhmt_phase_estimation_theorem11_sum_norm,
    ← bhmt_phase_estimation_theorem11_sum_norm,
    bhmt_phase_estimation_theorem11_state_normalized M ω hM] at he
  exact_mod_cast he

lemma bhmt_phase_estimation_theorem11_grid (M : ℕ) (ω : ℝ) (hM : 0 < M)
    (hω0 : 0 ≤ ω) (hω1 : ω < 1) (h : ∃ j : ℤ, (M : ℝ) * ω = (j : ℝ)) :
    ∃ x : Fin M, (x.val : ℝ) = (M : ℝ) * ω ∧ bhmt11OutcomeMass M ω x = 1 := by
  obtain ⟨j, hj⟩ := h
  have hm : (0 : ℝ) < M := by positivity
  have hj0 : 0 ≤ j := by exact_mod_cast (show (0 : ℝ) ≤ j by nlinarith)
  have hjM : j < (M : ℤ) := by exact_mod_cast (show (j : ℝ) < M by nlinarith)
  let x : Fin M := ⟨j.toNat, by omega⟩
  have hx : (x.val : ℝ) = (M : ℝ) * ω := by
    dsimp [x]
    have he : ((j.toNat : ℕ) : ℝ) = (j : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hj0
    rw [he]
    exact hj.symm
  refine ⟨x, hx, ?_⟩
  have ht : ω - x.val / (M : ℝ) = 0 := by
    apply sub_eq_zero.mpr
    apply (eq_div_iff (ne_of_gt hm)).mpr
    nlinarith
  rw [bhmt_phase_estimation_theorem11_mass_expSum M ω hM x, ht,
    bhmt_phase_estimation_theorem11_expSum_zero, Complex.norm_natCast,
    div_self (by positivity : (M : ℝ) ^ 2 ≠ 0)]

lemma bhmt_phase_estimation_theorem11_distance_small (u v : ℝ) (z : ℤ)
    (hz : |(z : ℝ) + v - u| ≤ 1 / 2) :
    bhmt11CircleDist u v = |(z : ℝ) + v - u| := by
  apply le_antisymm (bhmt_phase_estimation_theorem11_distance_le u v z)
  apply le_csInf (Set.range_nonempty _)
  rintro a ⟨j, rfl⟩
  by_cases h : j = z
  · subst j
    exact le_rfl
  have hi : (1 : ℝ) ≤ |((j - z : ℤ) : ℝ)| := by
    exact_mod_cast (show (1 : ℤ) ≤ |j - z| by have := abs_pos.mpr (sub_ne_zero.mpr h); omega)
  have htri := abs_sub_le ((j : ℝ) + v - u) 0 ((z : ℝ) + v - u)
  have he : (j : ℝ) + v - u - ((z : ℝ) + v - u) = ((j - z : ℤ) : ℝ) := by
    push_cast
    ring
  rw [he, sub_zero, zero_sub, abs_neg] at htri
  linarith

lemma bhmt_phase_estimation_theorem11_window_single (M : ℕ) (ω r : ℝ) (x : Fin M)
    (hx : bhmt11CircleDist (x.val / (M : ℝ)) ω ≤ r) :
    bhmt11OutcomeMass M ω x ≤ bhmt11WindowMass M ω r := by
  unfold bhmt11WindowMass
  have h := Finset.single_le_sum (s := (Finset.univ : Finset (Fin M)))
    (f := fun y => if bhmt11CircleDist (y.val / (M : ℝ)) ω ≤ r
      then bhmt11OutcomeMass M ω y else 0)
    (fun y _ => by (try dsimp only); split_ifs <;> first | exact bhmt_phase_estimation_theorem11_mass_nonneg M ω y | rfl)
    (Finset.mem_univ x)
  simpa [hx] using h

lemma bhmt_phase_estimation_theorem11_window_pair (M : ℕ) (ω r : ℝ) (x y : Fin M)
    (hxy : x ≠ y) (hx : bhmt11CircleDist (x.val / (M : ℝ)) ω ≤ r)
    (hy : bhmt11CircleDist (y.val / (M : ℝ)) ω ≤ r) :
    bhmt11OutcomeMass M ω x + bhmt11OutcomeMass M ω y ≤ bhmt11WindowMass M ω r := by
  classical
  let f := fun z : Fin M => if bhmt11CircleDist (z.val / (M : ℝ)) ω ≤ r
    then bhmt11OutcomeMass M ω z else 0
  have h := Finset.sum_le_sum_of_subset_of_nonneg (f := f)
    (Finset.subset_univ ({x, y} : Finset (Fin M)))
    (fun z _ _ => by dsimp [f]; split_ifs <;>
      first | exact bhmt_phase_estimation_theorem11_mass_nonneg M ω z | rfl)
  simpa [f, Finset.sum_pair hxy, hx, hy, bhmt11WindowMass] using h

lemma bhmt_phase_estimation_theorem11_nearest_labels (M : ℕ) (ω : ℝ) (hM : 2 < M)
    (hω0 : 0 ≤ ω) (hω1 : ω < 1) (hi : ¬ ∃ j : ℤ, (M : ℝ) * ω = (j : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ ∃ x y : Fin M, x ≠ y ∧
      bhmt11CircleDist (x.val / (M : ℝ)) ω = t / M ∧
      bhmt11CircleDist (y.val / (M : ℝ)) ω = (1 - t) / M := by
  have hm : (0 : ℝ) < M := by positivity
  have hm2 : (2 : ℝ) < M := by exact_mod_cast hM
  let n := ⌊(M : ℝ) * ω⌋₊
  let t := (M : ℝ) * ω - n
  have hn0 : (n : ℝ) ≤ (M : ℝ) * ω := Nat.floor_le (by positivity)
  have hn1 : (M : ℝ) * ω < n + 1 := Nat.lt_floor_add_one _
  have hnM : n < M := by exact_mod_cast (show (n : ℝ) < M by nlinarith)
  have ht0 : 0 < t := by
    have ht : 0 ≤ t := sub_nonneg.mpr hn0
    apply lt_of_le_of_ne ht
    intro he
    apply hi
    refine ⟨(n : ℤ), ?_⟩
    dsimp [t] at he
    norm_cast
    linarith
  have ht1 : t < 1 := by dsimp [t]; linarith
  have h1pos : 0 < 1 - t := by linarith
  have hd1 : t / M ≤ 1 / 2 := (div_le_iff₀ hm).mpr (by nlinarith)
  have hd2 : (1 - t) / M ≤ 1 / 2 := (div_le_iff₀ hm).mpr (by nlinarith)
  let x : Fin M := ⟨n, hnM⟩
  have hx : bhmt11CircleDist (x.val / (M : ℝ)) ω = t / M := by
    have he : (0 : ℝ) + ω - x.val / M = t / M := by
      dsimp [t, x]
      field_simp
      ring
    have hz : |(0 : ℝ) + ω - x.val / M| = t / M := by rw [he, abs_of_pos (div_pos ht0 hm)]
    simpa only [Int.cast_zero, hz] using
      bhmt_phase_estimation_theorem11_distance_small (x.val / (M : ℝ)) ω 0
        (by simpa only [Int.cast_zero, hz] using hd1)
  refine ⟨t, ht0, ht1, x, ?_⟩
  by_cases hn : n + 1 < M
  · let y : Fin M := ⟨n + 1, hn⟩
    refine ⟨y, (by intro h; have := congrArg Fin.val h; dsimp [x, y] at this; omega), hx, ?_⟩
    have he : (0 : ℝ) + ω - y.val / M = -((1 - t) / M) := by
      dsimp [y, t]
      push_cast
      field_simp
      ring
    have hz : |(0 : ℝ) + ω - y.val / M| = (1 - t) / M := by
      rw [he, abs_neg, abs_of_pos (div_pos h1pos hm)]
    simpa only [Int.cast_zero, hz] using
      bhmt_phase_estimation_theorem11_distance_small (y.val / (M : ℝ)) ω 0
        (by simpa only [Int.cast_zero, hz] using hd2)
  · have hn : n + 1 = M := by omega
    let y : Fin M := ⟨0, by omega⟩
    refine ⟨y, (by intro h; have := congrArg Fin.val h; dsimp [x, y] at this; omega), hx, ?_⟩
    have he : (-1 : ℝ) + ω - y.val / M = -((1 - t) / M) := by
      have hn' : (n : ℝ) + 1 = M := by exact_mod_cast hn
      dsimp [y, t]
      simp only [Nat.cast_zero, zero_div, sub_zero]
      field_simp
      nlinarith
    have hz : |(-1 : ℝ) + ω - y.val / M| = (1 - t) / M := by
      rw [he, abs_neg, abs_of_pos (div_pos h1pos hm)]
    simpa only [Int.cast_neg, Int.cast_one, hz] using
      bhmt_phase_estimation_theorem11_distance_small (y.val / (M : ℝ)) ω (-1)
        (by simpa only [Int.cast_neg, Int.cast_one, hz] using hd2)

noncomputable def bhmt_phase_estimation_theorem11_lift (M : ℕ) (ω : ℝ) (x : Fin M) : ℤ :=
  (x.val : ℤ) - (M : ℤ) * round (x.val / (M : ℝ) - ω)

lemma bhmt_phase_estimation_theorem11_lift_mod (M : ℕ) (ω : ℝ) (x : Fin M) :
    bhmt_phase_estimation_theorem11_lift M ω x % M = x.val := by
  have hx : (x.val : ℤ) % M = x.val :=
    Int.emod_eq_of_lt (by positivity) (by exact_mod_cast x.isLt)
  simp [bhmt_phase_estimation_theorem11_lift, Int.sub_emod, hx]

lemma bhmt_phase_estimation_theorem11_lift_injective (M : ℕ) (ω : ℝ) :
    Function.Injective (bhmt_phase_estimation_theorem11_lift M ω) := by
  intro x y h
  have he := congrArg (fun z : ℤ => z % M) h
  try dsimp only at he
  rw [bhmt_phase_estimation_theorem11_lift_mod, bhmt_phase_estimation_theorem11_lift_mod] at he
  exact Fin.ext (by exact_mod_cast he)

lemma bhmt_phase_estimation_theorem11_lift_spacing (M : ℕ) (ω : ℝ) (x y : Fin M)
    (hxy : x ≠ y) :
    (1 : ℝ) ≤ |(bhmt_phase_estimation_theorem11_lift M ω x : ℝ) -
      (bhmt_phase_estimation_theorem11_lift M ω y : ℝ)| := by
  have h : bhmt_phase_estimation_theorem11_lift M ω x ≠
      bhmt_phase_estimation_theorem11_lift M ω y :=
    fun h => hxy (bhmt_phase_estimation_theorem11_lift_injective M ω h)
  exact_mod_cast (show (1 : ℤ) ≤ |bhmt_phase_estimation_theorem11_lift M ω x - bhmt_phase_estimation_theorem11_lift M ω y| by have := abs_pos.mpr (sub_ne_zero.mpr h); omega)

lemma bhmt_phase_estimation_theorem11_scaled_distance (M : ℕ) (ω : ℝ) (hM : 0 < M)
    (x : Fin M) :
    (M : ℝ) * bhmt11CircleDist (x.val / (M : ℝ)) ω =
      |(bhmt_phase_estimation_theorem11_lift M ω x : ℝ) - (M : ℝ) * ω| := by
  have hm : (0 : ℝ) < M := by positivity
  rw [bhmt_phase_estimation_theorem11_distance_symm,
    bhmt_phase_estimation_theorem11_distance_round]
  calc
    _ = |(M : ℝ) * (x.val / (M : ℝ) - ω - round (x.val / (M : ℝ) - ω))| := by
      rw [abs_mul, abs_of_pos hm]
    _ = _ := by
      congr 1
      unfold bhmt_phase_estimation_theorem11_lift
      push_cast
      field_simp
      ring

lemma bhmt_phase_estimation_theorem11_tail (M : ℕ) (ω : ℝ) (hM : 0 < M)
    (k : ℝ) (hk : 1 < k) :
    1 - 1 / (2 * (k - 1)) ≤ bhmt11WindowMass M ω (k / (M : ℝ)) := by
  classical
  have hm : (0 : ℝ) < M := by positivity
  let f := fun x : Fin M => (M : ℝ) * bhmt11CircleDist (x.val / (M : ℝ)) ω
  let g := fun x : Fin M => (bhmt_phase_estimation_theorem11_lift M ω x : ℝ) - (M : ℝ) * ω
  let s := Finset.univ.filter (fun x : Fin M => k < f x)
  have hf (x : Fin M) : f x = |g x| := bhmt_phase_estimation_theorem11_scaled_distance M ω hM x
  have hpoint (x : Fin M) (hx : x ∈ s) :
      bhmt11OutcomeMass M ω x ≤ (1 / 4 : ℝ) * (1 / f x ^ 2) := by
    have hxk : k < f x := (Finset.mem_filter.mp hx).2
    have hd : 0 < bhmt11CircleDist (x.val / (M : ℝ)) ω := by
      dsimp [f] at hxk
      nlinarith
    have h := bhmt_phase_estimation_theorem11_mass_bound M ω hM x
      (by rw [bhmt_phase_estimation_theorem11_distance_symm]; exact hd)
    rw [bhmt_phase_estimation_theorem11_distance_symm ω (x.val / (M : ℝ))] at h
    convert! h using 1
    dsimp [f]
    field_simp
    ring
  have hb (a : Finset (Fin M)) (has : a ⊆ s)
      (hsep : ∀ x ∈ a, ∀ y ∈ a, x ≠ y → 1 ≤ |f x - f y|) :
      ∑ x ∈ a, bhmt11OutcomeMass M ω x ≤ (1 / 4 : ℝ) * (1 / (k - 1)) := by
    calc
      _ ≤ ∑ x ∈ a, (1 / 4 : ℝ) * (1 / f x ^ 2) :=
        Finset.sum_le_sum (fun x hx => hpoint x (has hx))
      _ = (1 / 4 : ℝ) * ∑ x ∈ a, 1 / f x ^ 2 := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (bhmt_phase_estimation_theorem11_spaced_tail a f k hk
          (fun x hx => ((Finset.mem_filter.mp (has hx)).2).le) hsep) (by norm_num)
  have hp : ∑ x ∈ s.filter (fun x => 0 ≤ g x), bhmt11OutcomeMass M ω x ≤
      (1 / 4 : ℝ) * (1 / (k - 1)) := by
    apply hb _ (Finset.filter_subset _ _)
    intro x hx y hy hxy
    have hx0 := (Finset.mem_filter.mp hx).2
    have hy0 := (Finset.mem_filter.mp hy).2
    rw [hf, hf, abs_of_nonneg hx0, abs_of_nonneg hy0]
    convert! bhmt_phase_estimation_theorem11_lift_spacing M ω x y hxy using 1
    congr 1
    dsimp [g]
    ring
  have hn : ∑ x ∈ s.filter (fun x => ¬ 0 ≤ g x), bhmt11OutcomeMass M ω x ≤
      (1 / 4 : ℝ) * (1 / (k - 1)) := by
    apply hb _ (Finset.filter_subset _ _)
    intro x hx y hy hxy
    have hx0 := (not_le.mp (Finset.mem_filter.mp hx).2).le
    have hy0 := (not_le.mp (Finset.mem_filter.mp hy).2).le
    rw [hf, hf, abs_of_nonpos hx0, abs_of_nonpos hy0]
    convert! bhmt_phase_estimation_theorem11_lift_spacing M ω y x (Ne.symm hxy) using 1
    congr 1
    dsimp [g]
    ring
  have ht : ∑ x ∈ s, bhmt11OutcomeMass M ω x ≤ 1 / (2 * (k - 1)) := by
    have he := Finset.sum_filter_add_sum_filter_not s (fun x => 0 ≤ g x)
      (fun x => bhmt11OutcomeMass M ω x)
    have hr : (1 / 4 : ℝ) * (1 / (k - 1)) + (1 / 4 : ℝ) * (1 / (k - 1)) =
        1 / (2 * (k - 1)) := by field_simp <;> ring
    linarith
  have htotal : bhmt11WindowMass M ω (k / (M : ℝ)) +
      ∑ x ∈ s, bhmt11OutcomeMass M ω x = 1 := by
    rw [← bhmt_phase_estimation_theorem11_normalization M ω hM]
    unfold bhmt11WindowMass
    dsimp [s]
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    have hc : k < f x ↔ ¬ bhmt11CircleDist (x.val / (M : ℝ)) ω ≤ k / M := by
      rw [not_le, div_lt_iff₀ hm]
      dsimp [f]
      rw [mul_comm]
    simp only [hc]
    by_cases h : bhmt11CircleDist (x.val / (M : ℝ)) ω ≤ k / M <;> simp [h]
  linarith

lemma bhmt_phase_estimation_theorem11_mass_lower (M : ℕ) (ω : ℝ) (hM : 0 < M)
    (x : Fin M) (t : ℝ) (ht : 0 < t)
    (hx : bhmt11CircleDist (x.val / (M : ℝ)) ω = t / M) :
    Real.sin (Real.pi * t) ^ 2 / (Real.pi ^ 2 * t ^ 2) ≤ bhmt11OutcomeMass M ω x := by
  have hm : (0 : ℝ) < M := by positivity
  have hd : 0 < bhmt11CircleDist ω (x.val / (M : ℝ)) := by
    rw [bhmt_phase_estimation_theorem11_distance_symm, hx]
    positivity
  have hdU : t / M ≤ 1 / 2 := by
    rw [← hx]
    exact (bhmt_phase_estimation_theorem11_distance_bounds _ _).2
  have hspos : 0 < Real.sin (t / M * Real.pi) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hden : (M : ℝ) ^ 2 * Real.sin (t / M * Real.pi) ^ 2 ≤ Real.pi ^ 2 * t ^ 2 := by
    have h := mul_le_mul_of_nonneg_left (Real.sin_sq_le_sq (x := t / M * Real.pi))
      (sq_nonneg (M : ℝ))
    have he : (M : ℝ) ^ 2 * (t / M * Real.pi) ^ 2 = Real.pi ^ 2 * t ^ 2 := by
      field_simp
    rwa [he] at h
  rw [bhmt_phase_estimation_theorem11_mass_formula M ω hM x hd,
    bhmt_phase_estimation_theorem11_distance_symm ω (x.val / (M : ℝ)), hx]
  have he : (M : ℝ) * (t / M) * Real.pi = Real.pi * t := by field_simp
  rw [he]
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden

lemma bhmt_phase_estimation_theorem11_scalar_quotient (t : ℝ) (ht : 0 < t) (ht' : t < 1) :
    8 / Real.pi ^ 2 ≤
      Real.sin (Real.pi * t) ^ 2 / (Real.pi ^ 2 * t ^ 2) +
      Real.sin (Real.pi * (1 - t)) ^ 2 / (Real.pi ^ 2 * (1 - t) ^ 2) := by
  have h := bhmt_phase_estimation_theorem11_scalar t ht ht'
  have ht0 : t ≠ 0 := ne_of_gt ht
  have ht1 : 1 - t ≠ 0 := by linarith
  rw [show Real.pi * (1 - t) = Real.pi - Real.pi * t by ring, Real.sin_pi_sub]
  convert! div_le_div_of_nonneg_right h
    (show 0 ≤ Real.pi ^ 2 * t ^ 2 * (1 - t) ^ 2 by positivity) using 1 <;>
    (try field_simp) <;> ring

lemma bhmt_phase_estimation_theorem11_nearest (M : ℕ) (ω : ℝ) (hM : 2 < M)
    (hω0 : 0 ≤ ω) (hω1 : ω < 1) :
    8 / Real.pi ^ 2 ≤ bhmt11WindowMass M ω (1 / (M : ℝ)) := by
  have hM0 : 0 < M := by omega
  have hm : (0 : ℝ) < M := by positivity
  by_cases hi : ∃ j : ℤ, (M : ℝ) * ω = (j : ℝ)
  · obtain ⟨x, hx, hx1⟩ := bhmt_phase_estimation_theorem11_grid M ω hM0 hω0 hω1 hi
    have hd : bhmt11CircleDist (x.val / (M : ℝ)) ω ≤ 1 / M := by
      have he : (x.val : ℝ) / M = ω := (div_eq_iff (ne_of_gt hm)).mpr (by nlinarith)
      rw [he, bhmt_phase_estimation_theorem11_distance_round]
      simp
    have h := bhmt_phase_estimation_theorem11_window_single M ω (1 / (M : ℝ)) x hd
    rw [hx1] at h
    have hp : 8 / Real.pi ^ 2 ≤ 1 := by
      apply (div_le_one (sq_pos_of_pos Real.pi_pos)).mpr
      nlinarith [Real.pi_gt_d2]
    exact hp.trans h
  · obtain ⟨t, ht, ht1, x, y, hxy, hx, hy⟩ :=
      bhmt_phase_estimation_theorem11_nearest_labels M ω hM hω0 hω1 hi
    have hpx := bhmt_phase_estimation_theorem11_mass_lower M ω hM0 x t ht hx
    have hpy := bhmt_phase_estimation_theorem11_mass_lower M ω hM0 y (1 - t) (by linarith) hy
    have hscalar := bhmt_phase_estimation_theorem11_scalar_quotient t ht ht1
    have hw := bhmt_phase_estimation_theorem11_window_pair M ω (1 / (M : ℝ)) x y hxy
      (by rw [hx]; exact div_le_div_of_nonneg_right ht1.le hm.le)
      (by rw [hy]; exact div_le_div_of_nonneg_right (by linarith) hm.le)
    linarith

theorem bhmt_phase_estimation_theorem11 :
  ∀ (M : ℕ) (ω : ℝ),
  0 < M → 0 ≤ ω → ω < 1 →
  (∑ x : Fin M, bhmt11OutcomeMass M ω x) = 1 ∧
  ((∃ j : ℤ, (M : ℝ) * ω = (j : ℝ)) →
    ∃ x : Fin M, (x.val : ℝ) = (M : ℝ) * ω ∧
      bhmt11OutcomeMass M ω x = 1) ∧
  ((¬ ∃ j : ℤ, (M : ℝ) * ω = (j : ℝ)) →
    ∀ x : Fin M,
      let Δ := bhmt11CircleDist ω ((x.val : ℝ) / (M : ℝ));
      bhmt11OutcomeMass M ω x =
        Real.sin ((M : ℝ) * Δ * Real.pi) ^ 2 /
          ((M : ℝ) ^ 2 * Real.sin (Δ * Real.pi) ^ 2) ∧
      bhmt11OutcomeMass M ω x ≤
        (1 : ℝ) / (2 * (M : ℝ) * Δ) ^ 2) ∧
  (∀ k : ℝ, 1 < k →
    1 - 1 / (2 * (k - 1)) ≤
      bhmt11WindowMass M ω (k / (M : ℝ))) ∧
  (2 < M →
    8 / Real.pi ^ 2 ≤ bhmt11WindowMass M ω (1 / (M : ℝ))) := by
  intro M ω hM hω0 hω1
  refine ⟨bhmt_phase_estimation_theorem11_normalization M ω hM,
    bhmt_phase_estimation_theorem11_grid M ω hM hω0 hω1, ?_,
    bhmt_phase_estimation_theorem11_tail M ω hM, ?_⟩
  · intro hi x
    (try dsimp only)
    have hd : 0 < bhmt11CircleDist ω (x.val / (M : ℝ)) := by
      apply lt_of_le_of_ne (bhmt_phase_estimation_theorem11_distance_bounds _ _).1
      intro he
      exact hi (bhmt_phase_estimation_theorem11_integral_of_distance_zero M ω hM x he.symm)
    exact ⟨bhmt_phase_estimation_theorem11_mass_formula M ω hM x hd,
      bhmt_phase_estimation_theorem11_mass_bound M ω hM x hd⟩
  · intro hM2
    exact bhmt_phase_estimation_theorem11_nearest M ω hM2 hω0 hω1

example : Theorem11Spec.expected :=
  bhmt_phase_estimation_theorem11

end Qatlib.Concepts.AmplitudeCore.PhaseEstimation
