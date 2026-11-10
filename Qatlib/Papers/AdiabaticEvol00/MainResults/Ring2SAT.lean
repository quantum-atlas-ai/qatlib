/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabaticEvol00.MainResults.AdiabaticDefs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AdiabaticEvol00.MainResults.Ring2SAT

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.AdiabaticEvol00.MainResults
open scoped Matrix.Norms.L2Operator ComplexOrder BigOperators

def ringBlock (θ s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(((s + s * Real.cos θ) : ℝ) : ℂ),
     (Complex.I * (((s * Real.sin θ) : ℝ) : ℂ));
     (-(Complex.I * (((s * Real.sin θ) : ℝ) : ℂ))),
     (((4 - 3 * s - s * Real.cos θ) : ℝ) : ℂ)]

theorem hermitian_two (a c d : ℝ) :
    (!![((a : ℝ) : ℂ), (Complex.I * ((c : ℝ) : ℂ));
        (-(Complex.I * ((c : ℝ) : ℂ))), ((d : ℝ) : ℂ)] :
      Matrix (Fin 2) (Fin 2) ℂ).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Complex.conj_I, Complex.conj_ofReal]

theorem ringBlock_isHermitian (θ s : ℝ) : (ringBlock θ s).IsHermitian :=
  hermitian_two (s + s * Real.cos θ) (s * Real.sin θ) (4 - 3 * s - s * Real.cos θ)

theorem ringBlock_trace (θ s : ℝ) :
    (ringBlock θ s).trace = ((4 - 2 * s : ℝ) : ℂ) := by
  simp [ringBlock, Matrix.trace, Fin.sum_univ_two]
  ring

theorem complex_i_mul_self_mul (z : ℂ) : Complex.I * z * (Complex.I * z) = -z ^ 2 := by
  have h : Complex.I * Complex.I = -1 := by
    rw [← pow_two]
    exact Complex.I_sq
  calc Complex.I * z * (Complex.I * z) = (Complex.I * Complex.I) * (z * z) := by ring
    _ = -1 * (z * z) := by rw [h]
    _ = -z ^ 2 := by ring

theorem ringBlock_det (θ s : ℝ) :
    (ringBlock θ s).det =
      (((s + s * Real.cos θ) * (4 - 3 * s - s * Real.cos θ) -
        (s * Real.sin θ) ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two]
  simp [ringBlock]
  rw [complex_i_mul_self_mul ((s : ℂ) * Complex.sin (θ : ℂ))]
  ring

theorem ringBlock_det_real (θ s : ℝ) :
    (s + s * Real.cos θ) * (4 - 3 * s - s * Real.cos θ) - (s * Real.sin θ) ^ 2 =
      4 * s * (1 - s) * (1 + Real.cos θ) := by
  linear_combination (-(s ^ 2)) * Real.sin_sq_add_cos_sq θ

theorem ringBlock_det_closed (θ s : ℝ) :
    (ringBlock θ s).det = ((4 * s * (1 - s) * (1 + Real.cos θ) : ℝ) : ℂ) := by
  rw [ringBlock_det, ringBlock_det_real]

def ringRadicand (θ s : ℝ) : ℝ :=
  (2 - 3 * s) ^ 2 + 4 * s * (1 - s) * (1 - Real.cos θ)

def ringEnergyPlus (θ s : ℝ) : ℝ := 2 - s + Real.sqrt (ringRadicand θ s)

def ringEnergyMinus (θ s : ℝ) : ℝ := 2 - s - Real.sqrt (ringRadicand θ s)

theorem ringEnergy_sum (θ s : ℝ) :
    ringEnergyPlus θ s + ringEnergyMinus θ s = 4 - 2 * s := by
  unfold ringEnergyPlus ringEnergyMinus
  ring

theorem ringEnergy_product (θ s : ℝ) (hR : 0 ≤ ringRadicand θ s) :
    ringEnergyPlus θ s * ringEnergyMinus θ s = 4 * s * (1 - s) * (1 + Real.cos θ) := by
  unfold ringEnergyPlus ringEnergyMinus
  have h : Real.sqrt (ringRadicand θ s) ^ 2 = ringRadicand θ s := Real.sq_sqrt hR
  unfold ringRadicand at h
  unfold ringRadicand
  nlinarith [h]

theorem ringBlock_spectrum (θ s : ℝ) (hR : 0 ≤ ringRadicand θ s) :
    (ringBlock θ s).trace = ((ringEnergyPlus θ s + ringEnergyMinus θ s : ℝ) : ℂ) ∧
    (ringBlock θ s).det = ((ringEnergyPlus θ s * ringEnergyMinus θ s : ℝ) : ℂ) := by
  constructor
  · rw [ringBlock_trace, ringEnergy_sum]
  · rw [ringBlock_det_closed, ringEnergy_product θ s hR]

theorem ringRadicand_two_thirds (θ : ℝ) :
    ringRadicand θ (2 / 3) = 8 / 9 * (1 - Real.cos θ) := by
  unfold ringRadicand
  ring

def ringGapFormula (n : ℕ) : ℝ :=
  ringEnergyPlus (Real.pi / n) (2 / 3) - ringEnergyMinus (Real.pi / n) (2 / 3)

theorem ringGapFormula_eq (n : ℕ) :
    ringGapFormula n = 2 * Real.sqrt (ringRadicand (Real.pi / n) (2 / 3)) := by
  unfold ringGapFormula ringEnergyPlus ringEnergyMinus
  ring

theorem ringEnergy_gap (θ s : ℝ) :
    ringEnergyPlus θ s - ringEnergyMinus θ s = 2 * Real.sqrt (ringRadicand θ s) := by
  unfold ringEnergyPlus ringEnergyMinus
  ring

theorem ringRadicand_pos {θ : ℝ} (hθ : Real.cos θ ≠ 1) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 < ringRadicand θ s := by
  intro s hs
  have hc : 0 < 1 - Real.cos θ := by
    have hlt : Real.cos θ < 1 := lt_of_le_of_ne (Real.cos_le_one θ) hθ
    linarith
  have hs0 : 0 ≤ s := hs.1
  have hs1 : 0 ≤ 1 - s := by linarith [hs.2]
  unfold ringRadicand
  rcases lt_or_eq_of_le hs0 with h | h
  · rcases lt_or_eq_of_le hs1 with h1 | h1
    · have hprod : 0 < 4 * s * (1 - s) * (1 - Real.cos θ) := by
        have h4s : 0 < 4 * s := by linarith
        exact mul_pos (mul_pos h4s h1) hc
      have hsq : 0 ≤ (2 - 3 * s) ^ 2 := sq_nonneg _
      linarith
    · have hseq : s = 1 := by linarith
      subst hseq
      norm_num
  · have hseq : s = 0 := by linarith
    subst hseq
    norm_num

theorem ringRadicand_complete_square (θ s : ℝ) :
    ringRadicand θ s =
      (9 - 4 * (1 - Real.cos θ)) *
          (s - (6 - 2 * (1 - Real.cos θ)) / (9 - 4 * (1 - Real.cos θ))) ^ 2 +
        4 * (1 - Real.cos θ) * (2 - (1 - Real.cos θ)) / (9 - 4 * (1 - Real.cos θ)) := by
  unfold ringRadicand
  have hA : 9 - 4 * (1 - Real.cos θ) ≠ 0 := by
    have hle : Real.cos θ ≤ 1 := Real.cos_le_one θ
    have hge : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
    nlinarith
  field_simp
  ring

theorem ringRadicand_vertex (θ : ℝ) :
    ringRadicand θ ((6 - 2 * (1 - Real.cos θ)) / (9 - 4 * (1 - Real.cos θ))) =
      4 * (1 - Real.cos θ) * (2 - (1 - Real.cos θ)) / (9 - 4 * (1 - Real.cos θ)) := by
  rw [ringRadicand_complete_square]
  simp

theorem ring_vertex_mem {θ : ℝ} (hcos : 0 ≤ Real.cos θ) :
    (6 - 2 * (1 - Real.cos θ)) / (9 - 4 * (1 - Real.cos θ)) ∈ Set.Icc (0 : ℝ) 1 := by
  have hle : Real.cos θ ≤ 1 := Real.cos_le_one θ
  constructor
  · apply div_nonneg <;> nlinarith
  · rw [div_le_one (by nlinarith)]
    nlinarith

theorem ringRadicand_vertex_le {θ s : ℝ} (hcos : 0 ≤ Real.cos θ) :
    ringRadicand θ ((6 - 2 * (1 - Real.cos θ)) / (9 - 4 * (1 - Real.cos θ))) ≤
      ringRadicand θ s := by
  rw [ringRadicand_vertex]
  have hA : 0 ≤ 9 - 4 * (1 - Real.cos θ) := by
    have hle : Real.cos θ ≤ 1 := Real.cos_le_one θ
    nlinarith
  have hsq : 0 ≤ (s - (6 - 2 * (1 - Real.cos θ)) / (9 - 4 * (1 - Real.cos θ))) ^ 2 :=
    sq_nonneg _
  have h := mul_nonneg hA hsq
  rw [ringRadicand_complete_square]
  linarith

theorem ringRadicand_vertex_sin (θ : ℝ) :
    4 * (1 - Real.cos θ) * (2 - (1 - Real.cos θ)) / (9 - 4 * (1 - Real.cos θ)) =
      4 * Real.sin θ ^ 2 / (5 + 4 * Real.cos θ) := by
  have hsin : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
    have h := Real.sin_sq_add_cos_sq θ
    linarith
  have hd : 9 - 4 * (1 - Real.cos θ) = 5 + 4 * Real.cos θ := by ring
  have hden : 5 + 4 * Real.cos θ ≠ 0 := by
    have hge : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
    nlinarith
  rw [hd, hsin]
  field_simp [hden]
  ring

theorem ringBlockGap_min (θ : ℝ) (hcos : 0 ≤ Real.cos θ) (s : ℝ) :
    2 * Real.sqrt (4 * Real.sin θ ^ 2 / (5 + 4 * Real.cos θ)) ≤
      ringEnergyPlus θ s - ringEnergyMinus θ s := by
  rw [ringEnergy_gap]
  have hv := ringRadicand_vertex_le (θ := θ) (s := s) hcos
  rw [ringRadicand_vertex] at hv
  rw [ringRadicand_vertex_sin] at hv
  have := Real.sqrt_le_sqrt hv
  linarith

theorem ringBlockGap_min_exact (θ : ℝ) (h0 : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    2 * Real.sqrt (4 * Real.sin θ ^ 2 / (5 + 4 * Real.cos θ)) =
      4 * Real.sin θ / Real.sqrt (5 + 4 * Real.cos θ) := by
  have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi h0 hπ
  have hden : 0 < 5 + 4 * Real.cos θ := by
    have hge : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
    nlinarith
  have hsq : 4 * Real.sin θ ^ 2 = (2 * Real.sin θ) ^ 2 := by ring
  rw [hsq, Real.sqrt_div' _ (le_of_lt hden), Real.sqrt_sq (by positivity)]
  ring

theorem ringRadicand_two_thirds_sq (θ : ℝ) :
    ringRadicand θ (2 / 3) = ((4 / 3) * Real.sin (θ / 2)) ^ 2 := by
  rw [ringRadicand_two_thirds]
  have h : 1 - Real.cos θ = 2 * Real.sin (θ / 2) ^ 2 := by
    have hc := Real.cos_two_mul_eq_one_sub (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at hc
    linarith
  rw [h]
  ring

theorem ringGapFormula_eq_sin (n : ℕ) (hn : 1 ≤ n) :
    ringGapFormula n = 8 / 3 * Real.sin (Real.pi / (2 * (n : ℝ))) := by
  rw [ringGapFormula_eq, ringRadicand_two_thirds_sq]
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpipos : 0 < Real.pi := Real.pi_pos
  have hx0 : 0 ≤ Real.pi / (n : ℝ) / 2 := by positivity
  have hxπ : Real.pi / (n : ℝ) / 2 ≤ Real.pi := by
    have h1 : Real.pi / (n : ℝ) ≤ Real.pi := by
      rw [div_le_iff₀ hnpos]
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      simpa using mul_le_mul_of_nonneg_left hn1 (le_of_lt Real.pi_pos)
    linarith
  have hsin : 0 ≤ Real.sin (Real.pi / (n : ℝ) / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx0 hxπ
  rw [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (4 / 3) * Real.sin (Real.pi / (n : ℝ) / 2))]
  have harg : Real.pi / (n : ℝ) / 2 = Real.pi / (2 * (n : ℝ)) := by
    field_simp
  rw [harg]
  ring

theorem tendsto_sin_div_pi :
    Filter.Tendsto
      (fun n : ℕ => Real.sin (Real.pi / (2 * (n : ℝ))) / (Real.pi / (2 * (n : ℝ))))
      Filter.atTop (nhds 1) := by
  have harg : Filter.Tendsto (fun n : ℕ => Real.pi / (2 * (n : ℝ))) Filter.atTop (nhds 0) := by
    have h := tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (Real.pi / 2)
    refine h.congr' ?_
    filter_upwards with n
    field_simp
  have hsinc : Filter.Tendsto (fun x : ℝ => Real.sinc x) (nhds 0) (nhds 1) := by
    simpa using Real.continuous_sinc.tendsto (0 : ℝ)
  have hcomp := hsinc.comp harg
  refine hcomp.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hne : Real.pi / (2 * (n : ℝ)) ≠ 0 := by
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    positivity
  change Real.sinc (Real.pi / (2 * (n : ℝ))) =
    Real.sin (Real.pi / (2 * (n : ℝ))) / (Real.pi / (2 * (n : ℝ)))
  rw [Real.sinc_of_ne_zero hne]

theorem ring_gap_asymptotic :
    Filter.Tendsto
      (fun n : ℕ => ringGapFormula n / (4 * Real.pi / (3 * (n : ℝ))))
      Filter.atTop (nhds 1) := by
  refine (tendsto_sin_div_pi).congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpipos : 0 < Real.pi := Real.pi_pos
  rw [ringGapFormula_eq_sin n hn]
  field_simp
  ring

theorem ring_required_time_cubic {E g : ℝ} {n : ℕ} (hn : 0 < (n : ℝ))
    (hE : E ≤ (n : ℝ)) (hg : 1 / (n : ℝ) ≤ g) (hE0 : 0 ≤ E) :
    E / g ^ 2 ≤ (n : ℝ) ^ 3 :=
  ring_time_is_cubic hn hE hg hE0

end Qatlib.Papers.AdiabaticEvol00.MainResults.Ring2SAT
