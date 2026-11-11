/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PhaseEstimation.Theorem11Quan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.NormNum

set_option backward.isDefEq.respectTransparency false

/-!
# SublinearPart22 — Corollary A.2 (phase-estimation probability bounds)

Fixed paper: arXiv:2207.08643v1, Appendix A, Lemma A.1 / Equation (13) and
Corollary A.2, PDF pp. 20–21.

Lemma A.1 (Kitaev; BHMT) states that with a power-of-two precision `t` the
phase-estimation algorithm outputs `i/t` with probability
`p(i) = sin²(t Δᵢ π) / (t² sin²(Δᵢ π))`, where `Δᵢ` is the circular distance
between `θ` and `i/t`.  Corollary A.2 then asserts, for `t ≥ 8`:
`p(i) ≥ 0.22` whenever `Δᵢ ≤ 5/(8t)`, and `p(i) ≤ 0.11` whenever `Δᵢ ≥ 1/t`.

We take Equation (13) at face value, with the continuous (`Δ = 0`) value `1`
(the exact-outcome branch), and prove both bounds with one-variable real
analysis.  The closed form is also bridged to the frozen formalization of
BHMT Theorem 11 (`bhmt11OutcomeMass`) in the non-degenerate case.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Qatlib.Concepts.AmplitudeCore.PhaseEstimation

namespace Qatlib.Papers.SublinearPart22.MainResults

/-- Equation (13) of arXiv:2207.08643v1: the phase-estimation outcome
probability `p(i)`, written with the continuous value `1` at `Δᵢ = 0`
(where the rational formula is `0/0`). -/
noncomputable def qpeOutcomeProb (t : ℕ) (θ : ℝ) (i : Fin t) : ℝ :=
  let Δ := bhmt11CircleDist θ ((i.val : ℝ) / (t : ℝ))
  if Δ = 0 then 1
  else Real.sin ((t : ℝ) * Δ * Real.pi) ^ 2 /
    ((t : ℝ) ^ 2 * Real.sin (Δ * Real.pi) ^ 2)

/-- In the non-degenerate case, Equation (13) is exactly the frozen BHMT
Theorem 11 outcome mass. -/
theorem qpeOutcomeProb_eq_outcomeMass_of_pos
    (t : ℕ) (θ : ℝ) (i : Fin t) (ht : 0 < t)
    (hd : 0 < bhmt11CircleDist θ ((i.val : ℝ) / (t : ℝ))) :
    qpeOutcomeProb t θ i = bhmt11OutcomeMass t θ i := by
  rw [qpeOutcomeProb, if_neg (ne_of_gt hd),
    bhmt_phase_estimation_theorem11_mass_formula t θ ht i hd]

/-- `sin (5π/8) = cos (π/8)`. -/
private lemma sin_five_pi_div_eight :
    Real.sin (5 * Real.pi / 8) = Real.cos (Real.pi / 8) := by
  have h : (5 * Real.pi / 8) = Real.pi / 8 + Real.pi / 2 := by ring
  rw [h, Real.sin_add_pi_div_two]

/-- `cos (π/8) = √(2+√2)/2`. -/
private lemma cos_pi_div_eight_eq : Real.cos (Real.pi / 8) = Real.sqrt (2 + Real.sqrt 2) / 2 :=
  Real.cos_pi_div_eight

/-- `cos²(π/8) = (2 + √2)/4`. -/
private lemma cos_pi_div_eight_sq : Real.cos (Real.pi / 8) ^ 2 = (2 + Real.sqrt 2) / 4 := by
  rw [cos_pi_div_eight_eq]
  rw [div_pow, Real.sq_sqrt (by positivity)]
  norm_num

/-- Numerical lower bound for the squared cos of `π/8`: `0.8535 < cos²(π/8)`. -/
private lemma cos_pi_div_eight_sq_lower : (0.8535 : ℝ) < Real.cos (Real.pi / 8) ^ 2 := by
  rw [cos_pi_div_eight_sq]
  have h : (707 / 500 : ℝ) < Real.sqrt 2 :=
    Real.lt_sqrt_of_sq_lt (by norm_num)
  nlinarith

/-- The lower-bound constant `s₀ = sin(5π/8)/(5π/8)` satisfies `s₀² ≥ 0.22`. -/
private lemma s0_sq_ge : (0.22 : ℝ) ≤
    (Real.sin (5 * Real.pi / 8) / (5 * Real.pi / 8)) ^ 2 := by
  rw [sin_five_pi_div_eight, div_pow]
  have hLpos : (0 : ℝ) < 5 * Real.pi / 8 := by positivity
  have hLsqpos : (0 : ℝ) < (5 * Real.pi / 8) ^ 2 := by positivity
  have hLlt : (5 * Real.pi / 8) ^ 2 < 3.85533225 := by
    have hπ : Real.pi < 3.1416 := Real.pi_lt_d4
    have h5 : 5 * Real.pi / 8 < 1.9635 := by linarith
    have h5pos : (0 : ℝ) ≤ 5 * Real.pi / 8 := by positivity
    have := pow_lt_pow_left₀ h5 h5pos (n := 2) two_ne_zero
    nlinarith
  rw [le_div_iff₀ hLsqpos]
  have hcos := cos_pi_div_eight_sq_lower
  nlinarith

/-- The lower-bound constant is at most `2/π` (needed for the `x ≤ π/2` branch). -/
private lemma s0_le_two_div_pi :
    Real.sin (5 * Real.pi / 8) / (5 * Real.pi / 8) ≤ 2 / Real.pi := by
  rw [sin_five_pi_div_eight]
  have hpos : (0 : ℝ) < 5 * Real.pi / 8 := by positivity
  have hcosle : Real.cos (Real.pi / 8) ≤ 1 := Real.cos_le_one _
  have h1 : Real.cos (Real.pi / 8) / (5 * Real.pi / 8) ≤ 1 / (5 * Real.pi / 8) :=
    div_le_div_of_nonneg_right hcosle (le_of_lt hpos)
  have h2 : (1 : ℝ) / (5 * Real.pi / 8) ≤ 2 / Real.pi := by
    rw [div_le_iff₀ hpos]
    have heq : (2 / Real.pi) * (5 * Real.pi / 8) = 5 / 4 := by
      field_simp
      norm_num
    rw [heq]
    norm_num
  linarith

/-- Analytic lower bound for Equation (13) when `Δ > 0` and `Δ ≤ 5/(8t)`. -/
private lemma qpe_prob_lower_of_pos
    (t : ℕ) (ht : 8 ≤ t) (θ : ℝ) (i : Fin t)
    (hd : 0 < bhmt11CircleDist θ ((i.val : ℝ) / (t : ℝ)))
    (hle : bhmt11CircleDist θ ((i.val : ℝ) / (t : ℝ)) ≤ 5 / (8 * (t : ℝ))) :
    (0.22 : ℝ) ≤ qpeOutcomeProb t θ i := by
  have ht0 : 0 < t := by omega
  have htR : (8 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht0
  set D := bhmt11CircleDist θ ((i.val : ℝ) / (t : ℝ)) with hD
  rw [qpeOutcomeProb, if_neg (ne_of_gt hd)]
  set y : ℝ := D * Real.pi with hy
  set x : ℝ := (t : ℝ) * D * Real.pi with hx
  have hx_eq : x = (t : ℝ) * y := by rw [hx, hy]; ring
  have hypos : 0 < y := by rw [hy]; positivity
  have hDt : D ≤ 5 / 8 := by
    have h8t : (8 : ℝ) ≤ 8 * (t : ℝ) := by nlinarith [htR]
    have : 5 / (8 * (t : ℝ)) ≤ 5 / 8 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) h8t
    linarith
  have hyle : y ≤ 5 * Real.pi / 8 := by
    rw [hy]
    nlinarith [hDt, Real.pi_pos]
  have hylt : y < Real.pi := by
    have h5 : 5 * Real.pi / 8 < Real.pi := by nlinarith [Real.pi_pos]
    linarith
  have hsinypos : 0 < Real.sin y := Real.sin_pos_of_pos_of_lt_pi hypos hylt
  have hxpos : 0 < x := by rw [hx_eq]; positivity
  have hxle : x ≤ 5 * Real.pi / 8 := by
    rw [hx]
    have h1 : D * Real.pi ≤ (5 / (8 * (t : ℝ))) * Real.pi :=
      mul_le_mul_of_nonneg_right hle (le_of_lt Real.pi_pos)
    have h2 : (t : ℝ) * (D * Real.pi) ≤ (t : ℝ) * ((5 / (8 * (t : ℝ))) * Real.pi) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt htpos)
    have heq : (t : ℝ) * ((5 / (8 * (t : ℝ))) * Real.pi) = 5 * Real.pi / 8 := by
      field_simp
    nlinarith
  have hs0_sq := s0_sq_ge
  have hs0_nonneg : (0 : ℝ) ≤ Real.sin (5 * Real.pi / 8) / (5 * Real.pi / 8) := by
    apply div_nonneg
    · exact le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos]))
    · positivity
  have hsinx_lb : Real.sin (5 * Real.pi / 8) / (5 * Real.pi / 8) * x ≤ Real.sin x := by
    by_cases hx_half : x ≤ Real.pi / 2
    · have hjordan : 2 / Real.pi * x ≤ Real.sin x := Real.mul_le_sin (le_of_lt hxpos) hx_half
      have hs0le := s0_le_two_div_pi
      have hmono2 : Real.sin (5 * Real.pi / 8) / (5 * Real.pi / 8) * x ≤ 2 / Real.pi * x :=
        mul_le_mul_of_nonneg_right hs0le (le_of_lt hxpos)
      linarith
    · push Not at hx_half
      have hx_pi : x < Real.pi := by nlinarith [Real.pi_pos]
      have hmono : Real.sin (3 * Real.pi / 8) ≤ Real.sin (Real.pi - x) := by
        apply Real.sin_le_sin_of_le_of_le_pi_div_two
        · nlinarith [Real.pi_pos]
        · nlinarith
        · nlinarith
      have heq : Real.sin (5 * Real.pi / 8) = Real.sin (3 * Real.pi / 8) := by
        have := Real.sin_pi_sub (5 * Real.pi / 8)
        rw [show Real.pi - 5 * Real.pi / 8 = 3 * Real.pi / 8 by ring] at this
        exact this.symm
      have h1 : Real.sin (5 * Real.pi / 8) / (5 * Real.pi / 8) * x ≤
          Real.sin (5 * Real.pi / 8) := by
        have hm := mul_le_mul_of_nonneg_left hxle hs0_nonneg
        have hlin : Real.sin (5 * Real.pi / 8) / (5 * Real.pi / 8) * (5 * Real.pi / 8) =
            Real.sin (5 * Real.pi / 8) := by
          field_simp
        linarith
      have h2 : Real.sin (5 * Real.pi / 8) ≤ Real.sin (Real.pi - x) := by
        rw [heq]; exact hmono
      calc Real.sin (5 * Real.pi / 8) / (5 * Real.pi / 8) * x
          ≤ Real.sin (5 * Real.pi / 8) := h1
        _ ≤ Real.sin (Real.pi - x) := h2
        _ = Real.sin x := Real.sin_pi_sub x
  have hsinx_sq : (Real.sin (5 * Real.pi / 8) / (5 * Real.pi / 8) * x) ^ 2 ≤
      Real.sin x ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hs0_nonneg (le_of_lt hxpos)) hsinx_lb 2
  have hs0x_sq : (Real.sin (5 * Real.pi / 8) / (5 * Real.pi / 8) * x) ^ 2 =
      (Real.sin (5 * Real.pi / 8) / (5 * Real.pi / 8)) ^ 2 * x ^ 2 := by ring
  have hx2 : x ^ 2 = (t : ℝ) ^ 2 * y ^ 2 := by rw [hx_eq]; ring
  have hsin_le : Real.sin y ≤ y := Real.sin_le (le_of_lt hypos)
  have hysq : Real.sin y ^ 2 ≤ y ^ 2 :=
    pow_le_pow_left₀ (le_of_lt hsinypos) hsin_le 2
  rw [le_div_iff₀ (by positivity)]
  have hkey : (0.22 : ℝ) * ((t : ℝ) ^ 2 * Real.sin y ^ 2) ≤ Real.sin x ^ 2 := by
    have h1 : (0.22 : ℝ) * ((t : ℝ) ^ 2 * Real.sin y ^ 2) ≤
        0.22 * ((t : ℝ) ^ 2 * y ^ 2) := by
      have : (t : ℝ) ^ 2 * Real.sin y ^ 2 ≤ (t : ℝ) ^ 2 * y ^ 2 :=
        mul_le_mul_of_nonneg_left hysq (by positivity)
      nlinarith
    have h2 : (0.22 : ℝ) * ((t : ℝ) ^ 2 * y ^ 2) ≤
        (Real.sin (5 * Real.pi / 8) / (5 * Real.pi / 8)) ^ 2 * ((t : ℝ) ^ 2 * y ^ 2) := by
      exact mul_le_mul_of_nonneg_right hs0_sq (by positivity)
    have h3 : (Real.sin (5 * Real.pi / 8) / (5 * Real.pi / 8)) ^ 2 * ((t : ℝ) ^ 2 * y ^ 2) ≤
        Real.sin x ^ 2 := by
      calc (Real.sin (5 * Real.pi / 8) / (5 * Real.pi / 8)) ^ 2 * ((t : ℝ) ^ 2 * y ^ 2)
          = (Real.sin (5 * Real.pi / 8) / (5 * Real.pi / 8) * x) ^ 2 := by
              rw [hs0x_sq, hx2]
        _ ≤ Real.sin x ^ 2 := hsinx_sq
    linarith
  exact hkey

/-- Analytic upper bound for Equation (13) when `Δ ≥ 1/t`. -/
private lemma qpe_prob_upper_of_pos
    (t : ℕ) (ht : 8 ≤ t) (θ : ℝ) (i : Fin t)
    (hd : 0 < bhmt11CircleDist θ ((i.val : ℝ) / (t : ℝ)))
    (hge : 1 / (t : ℝ) ≤ bhmt11CircleDist θ ((i.val : ℝ) / (t : ℝ))) :
    qpeOutcomeProb t θ i ≤ 0.11 := by
  have ht0 : 0 < t := by omega
  have htR : (8 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht0
  set D := bhmt11CircleDist θ ((i.val : ℝ) / (t : ℝ)) with hD
  have hdU : D ≤ 1 / 2 := (bhmt_phase_estimation_theorem11_distance_bounds θ _).2
  rw [qpeOutcomeProb, if_neg (ne_of_gt hd)]
  set y : ℝ := D * Real.pi with hy
  set x : ℝ := (t : ℝ) * D * Real.pi with hx
  have hypos : 0 < y := by rw [hy]; positivity
  have hyle : y ≤ Real.pi / 2 := by rw [hy]; nlinarith [hdU, Real.pi_pos]
  have hpt : Real.pi / (t : ℝ) ≤ y := by
    rw [hy]
    have hmul : (1 / (t : ℝ)) * Real.pi ≤ D * Real.pi :=
      mul_le_mul_of_nonneg_right hge (le_of_lt Real.pi_pos)
    have heq : (1 / (t : ℝ)) * Real.pi = Real.pi / (t : ℝ) := by ring
    linarith
  have hptpos : 0 < Real.pi / (t : ℝ) := by positivity
  have hsin_mono : Real.sin (Real.pi / (t : ℝ)) ≤ Real.sin y := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · nlinarith [Real.pi_pos]
    · exact hyle
    · exact hpt
  have hsiny_pos : 0 < Real.sin y := Real.sin_pos_of_pos_of_lt_pi hypos (by nlinarith [hyle])
  have htsin_gt : (3.02 : ℝ) < (t : ℝ) * Real.sin (Real.pi / (t : ℝ)) := by
    have hsin_gt : Real.pi / (t : ℝ) - (Real.pi / (t : ℝ)) ^ 3 / 4 <
        Real.sin (Real.pi / (t : ℝ)) := by
      nlinarith [Real.sin_gt_sub_cube hptpos, pow_pos hptpos 3]
    have hmul : (t : ℝ) * (Real.pi / (t : ℝ) - (Real.pi / (t : ℝ)) ^ 3 / 4) <
        (t : ℝ) * Real.sin (Real.pi / (t : ℝ)) :=
      mul_lt_mul_of_pos_left hsin_gt htpos
    have hcoord : (t : ℝ) * (Real.pi / (t : ℝ) - (Real.pi / (t : ℝ)) ^ 3 / 4) =
        Real.pi - Real.pi ^ 3 / (4 * (t : ℝ) ^ 2) := by
      field_simp
    have hden_ge : Real.pi ^ 3 / (4 * (t : ℝ) ^ 2) ≤ Real.pi ^ 3 / 256 := by
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num) (by nlinarith [htR])
    have hpi_gt : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
    have hpi_lt : Real.pi < 3.1416 := Real.pi_lt_d4
    have hcube : Real.pi ^ 3 < 31.007 := by
      have h : Real.pi ^ 3 < (3.1416 : ℝ) ^ 3 :=
        pow_lt_pow_left₀ hpi_lt (le_of_lt Real.pi_pos) (n := 3) (by norm_num)
      norm_num at h
      linarith
    have hnum : (3.02 : ℝ) < Real.pi - Real.pi ^ 3 / (4 * (t : ℝ) ^ 2) := by
      nlinarith
    linarith [hmul, hcoord, hnum]
  have h1 : (1 : ℝ) / ((t : ℝ) ^ 2 * Real.sin (Real.pi / (t : ℝ)) ^ 2) <
      1 / (3.02) ^ 2 := by
    have hsq : (3.02 : ℝ) ^ 2 < (t : ℝ) ^ 2 * Real.sin (Real.pi / (t : ℝ)) ^ 2 := by
      have hp := pow_lt_pow_left₀ htsin_gt (by positivity) (n := 2) two_ne_zero
      have he : ((t : ℝ) * Real.sin (Real.pi / (t : ℝ))) ^ 2 =
          (t : ℝ) ^ 2 * Real.sin (Real.pi / (t : ℝ)) ^ 2 := by ring
      linarith [hp, he]
    exact one_div_lt_one_div_of_lt (by norm_num) hsq
  have h2 : (1 : ℝ) / (3.02) ^ 2 ≤ 0.11 := by norm_num
  have hsin_pt_nonneg : 0 ≤ Real.sin (Real.pi / (t : ℝ)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (le_of_lt hptpos) (by nlinarith [Real.pi_pos, htpos])
  have hden : (t : ℝ) ^ 2 * Real.sin (Real.pi / (t : ℝ)) ^ 2 ≤
      (t : ℝ) ^ 2 * Real.sin y ^ 2 := by
    have hs := pow_le_pow_left₀ hsin_pt_nonneg hsin_mono 2
    exact mul_le_mul_of_nonneg_left hs (by positivity)
  have hnum_le : Real.sin x ^ 2 ≤ 1 := Real.sin_sq_le_one x
  have hsin_pt_pos : 0 < Real.sin (Real.pi / (t : ℝ)) :=
    Real.sin_pos_of_pos_of_lt_pi hptpos (by nlinarith [Real.pi_pos, htpos])
  have hBpos : (0 : ℝ) < (t : ℝ) ^ 2 * Real.sin y ^ 2 :=
    mul_pos (by positivity) (pow_pos hsiny_pos 2)
  have hCpos : (0 : ℝ) < (t : ℝ) ^ 2 * Real.sin (Real.pi / (t : ℝ)) ^ 2 :=
    mul_pos (by positivity) (pow_pos hsin_pt_pos 2)
  have hmass_le : Real.sin x ^ 2 / ((t : ℝ) ^ 2 * Real.sin y ^ 2) ≤
      1 / ((t : ℝ) ^ 2 * Real.sin (Real.pi / (t : ℝ)) ^ 2) := by
    calc Real.sin x ^ 2 / ((t : ℝ) ^ 2 * Real.sin y ^ 2)
        ≤ 1 / ((t : ℝ) ^ 2 * Real.sin y ^ 2) :=
          div_le_div_of_nonneg_right hnum_le (le_of_lt hBpos)
      _ ≤ 1 / ((t : ℝ) ^ 2 * Real.sin (Real.pi / (t : ℝ)) ^ 2) :=
          div_le_div_of_nonneg_left (by norm_num) hCpos hden
  exact le_trans hmass_le (le_of_lt (lt_of_lt_of_le h1 h2))

/-- **Corollary A.2** (arXiv:2207.08643v1, Appendix A, Eq. (13), p. 20):
if `t ≥ 8` then the phase-estimation distribution satisfies
`p(i) ≥ 0.22` when `Δᵢ ≤ 5/(8t)` and `p(i) ≤ 0.11` when `Δᵢ ≥ 1/t`. -/
theorem corollaryA2_qpe_probability_bounds
    (t : ℕ) (ht : 8 ≤ t) (θ : ℝ) (_hθ0 : 0 ≤ θ) (_hθ1 : θ < 1) (i : Fin t) :
    let Δ := bhmt11CircleDist θ ((i.val : ℝ) / (t : ℝ))
    (Δ ≤ 5 / (8 * (t : ℝ)) → (0.22 : ℝ) ≤ qpeOutcomeProb t θ i) ∧
    (1 / (t : ℝ) ≤ Δ → qpeOutcomeProb t θ i ≤ 0.11) := by
  intro Δ
  have hDnn : 0 ≤ Δ :=
    (bhmt_phase_estimation_theorem11_distance_bounds θ ((i.val : ℝ) / (t : ℝ))).1
  constructor
  · intro hle
    by_cases hzero : Δ = 0
    · rw [qpeOutcomeProb, if_pos hzero]
      norm_num
    · exact qpe_prob_lower_of_pos t ht θ i (lt_of_le_of_ne hDnn (Ne.symm hzero)) hle
  · intro hge
    have hpos : 0 < Δ := by
      have : (0 : ℝ) < 1 / (t : ℝ) := by
        apply one_div_pos.mpr
        exact_mod_cast (show (0 : ℕ) < t by omega)
      linarith
    exact qpe_prob_upper_of_pos t ht θ i hpos hge

end Qatlib.Papers.SublinearPart22.MainResults
