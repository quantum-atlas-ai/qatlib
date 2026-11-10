/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
import Mathlib.Analysis.Real.Pi.Bounds
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Qatlib.Concepts.PeriodSampling.DlogGoodProb
open scoped Classical BigOperators

theorem progression_grid_first (N : ℕ) :
    (∑ b : Fin N, (b.val : ℝ)) = (N : ℝ) * ((N : ℝ) - 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_succ]
    rw [ih]
    ring

theorem progression_grid_second (N : ℕ) :
    (∑ b : Fin N, (b.val : ℝ)^2) =
      (N : ℝ) * ((N : ℝ) - 1) * (2 * (N : ℝ) - 1) / 6 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_succ]
    rw [ih]
    ring

theorem progression_centered_second (N : ℕ) :
    (∑ b : Fin N, ((b.val : ℝ) - ((N : ℝ) - 1) / 2)^2) =
      (N : ℝ) * ((N : ℝ)^2 - 1) / 12 := by
  have hpoint (b : Fin N) : ((b.val : ℝ) - ((N : ℝ) - 1) / 2)^2 =
      (b.val : ℝ)^2 - ((N : ℝ) - 1) * (b.val : ℝ) + (((N : ℝ) - 1) / 2)^2 := by ring
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    progression_grid_first, progression_grid_second]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem progression_small_phase_bounds (η : ℝ) (hη : |η| ≤ Real.pi / 12) :
    (139 / 144 : ℝ) ≤ Real.cos η ∧ |Real.sin η| ≤ (4 / 15 : ℝ) := by
  have hpi : Real.pi ≤ (16 / 5 : ℝ) := by linarith [Real.pi_lt_d2]
  have hpisq : Real.pi^2 ≤ 10 := by
    have hsq := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d2.le (n := 2)
    norm_num at hsq
    linarith
  have hηsq : η^2 ≤ Real.pi^2 / 144 := by
    have h := (sq_le_sq₀ (abs_nonneg η) (by positivity : 0 ≤ Real.pi / 12)).mpr hη
    simpa only [sq_abs, div_pow, show (12 : ℝ)^2 = 144 by norm_num] using h
  constructor
  · nlinarith [Real.one_sub_sq_div_two_le_cos (x := η)]
  · exact (Real.abs_sin_le_abs (x := η)).trans (by linarith)

theorem progression_cos_perturbation (γ η : ℝ) (hγ : |γ| ≤ Real.pi / 2)
    (hη : |η| ≤ Real.pi / 12) :
    (139 / 144 : ℝ) * Real.cos γ - 4 / 15 ≤ Real.cos (γ + η) := by
  obtain ⟨hc, hs⟩ := progression_small_phase_bounds η hη
  have hcos : 0 ≤ Real.cos γ := Real.cos_nonneg_of_mem_Icc (abs_le.mp hγ)
  have hp := mul_le_mul_of_nonneg_left hc hcos
  have hsin : Real.sin γ * Real.sin η ≤ (4 / 15 : ℝ) := by
    calc
      _ ≤ |Real.sin γ * Real.sin η| := le_abs_self _
      _ = |Real.sin γ| * |Real.sin η| := abs_mul _ _
      _ ≤ 1 * (4 / 15 : ℝ) := mul_le_mul (Real.abs_sin_le_one _) hs (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  rw [Real.cos_add]
  nlinarith

theorem perturbed_progression_norm_lower (N q : ℕ) (hN : 0 < N) (hNq : N ≤ q)
    (θ s : ℝ) (hθ : |θ| ≤ 1/2) (hs : |s| ≤ (q : ℝ)/12)
    (a : Fin N → ℝ) (ha : ∀ b, 0 ≤ a b ∧ a b ≤ (N : ℝ)) :
    (N : ℝ)/4 ≤ ‖∑ b : Fin N, Complex.exp (Complex.I *
      ((2 * Real.pi * θ / (q : ℝ) * ((b.val : ℝ) - ((N : ℝ)-1)/2) +
        2 * Real.pi * (a b/(N : ℝ)-1/2) * s/(q : ℝ) : ℝ) : ℂ))‖ := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hq : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le hN hNq)
  have hNqR : (N : ℝ) ≤ q := by exact_mod_cast hNq
  have hpisq : Real.pi^2 ≤ 10 := by
    have hsq := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d2.le (n := 2)
    norm_num at hsq
    linarith
  let γ := fun b : Fin N => 2 * Real.pi * θ / (q : ℝ) * ((b.val : ℝ) - ((N : ℝ)-1)/2)
  let η := fun b : Fin N => 2 * Real.pi * (a b/(N : ℝ)-1/2) * s/(q : ℝ)
  have hcoef : |2 * Real.pi * θ / (q : ℝ)| ≤ Real.pi/(q : ℝ) := by
    rw [abs_div, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hq]
    norm_num only [show |(2 : ℝ)| = 2 by norm_num]
    apply div_le_div_of_nonneg_right _ hq.le
    nlinarith [Real.pi_pos]
  have hγ (b : Fin N) : |γ b| ≤ Real.pi/2 := by
    have hb : (b.val : ℝ) ≤ (N : ℝ)-1 := by
      have h := b.isLt
      have h' : b.val+1 ≤ N := by omega
      have h'R : (b.val : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast h'
      linarith
    have hb0 : (0 : ℝ) ≤ b.val := Nat.cast_nonneg _
    have hd : |(b.val : ℝ)-((N : ℝ)-1)/2| ≤ (N : ℝ)/2 := by
      apply abs_le.mpr
      constructor <;> linarith
    calc
      _ = |2*Real.pi*θ/(q : ℝ)| * |(b.val : ℝ)-((N : ℝ)-1)/2| := abs_mul _ _
      _ ≤ (Real.pi/(q : ℝ))*((N : ℝ)/2) :=
        mul_le_mul hcoef hd (abs_nonneg _) (by positivity)
      _ = (Real.pi/2)*((N : ℝ)/(q : ℝ)) := by ring
      _ ≤ (Real.pi/2)*1 := mul_le_mul_of_nonneg_left ((div_le_one hq).mpr hNqR) (by positivity)
      _ = _ := mul_one _
  have hη (b : Fin N) : |η b| ≤ Real.pi/12 := by
    have hd : |a b/(N : ℝ)-1/2| ≤ (1/2 : ℝ) := by
      have h0 := div_nonneg (ha b).1 hNR.le
      have h1 := (div_le_one hNR).mpr (ha b).2
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    calc
      _ = 2 * Real.pi * |a b/(N : ℝ)-1/2| * |s| / (q : ℝ) := by
        simp only [η, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hq,
            show |(2 : ℝ)| = 2 by norm_num]
      _ ≤ 2*Real.pi*(1/2)*((q : ℝ)/12)/(q : ℝ) := by gcongr
      _ = _ := by field_simp
  have hcoef2 : (2*Real.pi*θ/(q : ℝ))^2 ≤ 10/(q : ℝ)^2 := by
    have hsq := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ Real.pi/(q : ℝ))).mpr hcoef
    have hsq' : (2*Real.pi*θ/(q : ℝ))^2 ≤ Real.pi^2/(q : ℝ)^2 := by
      simpa only [sq_abs, div_pow] using hsq
    exact hsq'.trans (div_le_div_of_nonneg_right hpisq (sq_nonneg _))
  have hγ2 : (∑ b, γ b ^ 2) ≤ (5/6 : ℝ)*(N : ℝ) := by
    have hd : (∑ b : Fin N, ((b.val : ℝ)-((N : ℝ)-1)/2)^2) ≤ (N : ℝ)^3/12 := by
      rw [progression_centered_second]
      nlinarith
    simp only [γ, mul_pow, ← Finset.mul_sum]
    calc
      _ ≤ (10/(q : ℝ)^2)*((N : ℝ)^3/12) :=
        mul_le_mul hcoef2 hd (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
      _ = ((5/6 : ℝ)*(N : ℝ))*((N : ℝ)^2/(q : ℝ)^2) := by ring
      _ ≤ ((5/6 : ℝ)*(N : ℝ))*1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (div_le_one (sq_pos_of_pos hq)).mpr (pow_le_pow_left₀ hNR.le hNqR 2)
      _ = _ := mul_one _
  have hcos : (7/12 : ℝ)*(N : ℝ) ≤ ∑ b, Real.cos (γ b) := by
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N)))
      (fun b _ => Real.one_sub_sq_div_two_le_cos (x := γ b))
    simp only [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] at h
    linarith
  have hre (b : Fin N) : (Complex.exp (Complex.I * ((γ b + η b : ℝ) : ℂ))).re =
      Real.cos (γ b + η b) := by
    simp [Complex.exp_re, Complex.mul_re, Complex.mul_im]
  have hsum : (139/144 : ℝ)*(∑ b, Real.cos (γ b)) - (N : ℝ)*(4/15) ≤
      (∑ b, Complex.exp (Complex.I * ((γ b + η b : ℝ) : ℂ))).re := by
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N)))
      (fun b _ => progression_cos_perturbation (γ b) (η b) (hγ b) (hη b))
    simpa only [Complex.re_sum, hre, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h
  have hproject : (N : ℝ)/4 ≤
      (∑ b, Complex.exp (Complex.I * ((γ b + η b : ℝ) : ℂ))).re := by linarith
  exact hproject.trans (Complex.re_le_norm _)

end Qatlib.Concepts.PeriodSampling.DlogGoodProb
