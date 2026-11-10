/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PhaseEstimation.Theorem11Quan
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Complex.BigOperators
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.Trigonometric
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Qatlib.Concepts.AmplitudeCore.PhaseEstimation

namespace Qatlib.Papers.GroundState08.MainResults.MomentumInnerProduct

def momentumInner (k : ℕ) (φ μ : ℝ) : ℂ :=
  ∑ y : Fin (2 ^ k), star (bhmt11PhaseState (2 ^ k) φ y) *
    bhmt11PhaseState (2 ^ k) μ y

def momentumInnerAt (M : ℕ) (φ μ : ℝ) : ℂ :=
  ∑ y : Fin M, star (bhmt11PhaseState M φ y) * bhmt11PhaseState M μ y

lemma momentumInner_eq_at (k : ℕ) (φ μ : ℝ) :
    momentumInner k φ μ = momentumInnerAt (2 ^ k) φ μ := rfl

lemma momentumInnerAt_eq (M : ℕ) (φ μ : ℝ) :
    momentumInnerAt M φ μ =
      (M : ℂ)⁻¹ * bhmt_phase_estimation_theorem11_expSum M (μ - φ) := by
  have hs : (Real.sqrt (M : ℝ) : ℂ) * (Real.sqrt (M : ℝ) : ℂ) = (M : ℂ) := by
    norm_cast
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ M by positivity)]
  simp only [momentumInnerAt, bhmt11PhaseState, bhmt_phase_estimation_theorem11_expSum,
    Finset.mul_sum, star_mul, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro y _
  rw [← Complex.exp_conj]
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  have hfac : ∀ a b c : ℂ, a * c * (c * b) = (c * c) * (a * b) := by
    intro a b c; ring
  rw [hfac, ← Complex.exp_add, ← mul_inv_rev, hs]
  congr 2
  push_cast
  ring

lemma momentumInnerAt_norm_le (M : ℕ) (hM : 0 < M) (φ μ : ℝ)
    (hne : φ ≠ μ) (hsmall : |φ - μ| ≤ 1 / 2) :
    ‖momentumInnerAt M φ μ‖ ≤ 1 / (2 * (M : ℝ) * |φ - μ|) := by
  have hMreal : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have ht0 : μ - φ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have htabs : 0 < |μ - φ| := abs_pos.mpr ht0
  have htle : |μ - φ| ≤ 1 / 2 := by rw [abs_sub_comm]; exact hsmall

  have hne_exp : Complex.exp (((2 * Real.pi * (μ - φ) : ℝ) : ℂ) * Complex.I) ≠ 1 := by
    intro h
    rw [Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    have him := congrArg Complex.im hn
    simp at him
    have ht_eq : μ - φ = (n : ℝ) := by
      have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
      have heq : (2 * Real.pi) * (μ - φ) = (2 * Real.pi) * (n : ℝ) := by
        rw [him, mul_comm]
      exact mul_left_cancel₀ h2pi heq
    have hnz : n ≠ 0 := by
      intro hn0
      apply ht0
      rw [ht_eq, hn0]
      simp
    have habs : (1 : ℝ) ≤ |(n : ℝ)| := by
      exact_mod_cast Int.one_le_abs hnz
    rw [ht_eq] at htle
    have hle : (1 : ℝ) ≤ 1 / 2 := le_trans habs htle
    norm_num at hle
  have hgeo := bhmt_phase_estimation_theorem11_expSum_geometric M (μ - φ) hne_exp
  have hnum :
      ‖1 - Complex.exp (((2 * Real.pi * (μ - φ) : ℝ) : ℂ) * Complex.I) ^ M‖ ≤ 2 := by
    calc
      ‖1 - Complex.exp (((2 * Real.pi * (μ - φ) : ℝ) : ℂ) * Complex.I) ^ M‖ ≤
          ‖(1 : ℂ)‖ + ‖Complex.exp (((2 * Real.pi * (μ - φ) : ℝ) : ℂ) * Complex.I) ^ M‖ :=
        norm_sub_le _ _
      _ = 2 := by
        rw [norm_one, norm_pow, Complex.norm_exp_ofReal_mul_I, one_pow]
        norm_num
  have hdenpos :
      0 < ‖1 - Complex.exp (((2 * Real.pi * (μ - φ) : ℝ) : ℂ) * Complex.I)‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hne_exp))
  have hden : 4 * |μ - φ| ≤
      ‖1 - Complex.exp (((2 * Real.pi * (μ - φ) : ℝ) : ℂ) * Complex.I)‖ := by
    have hchord := Complex.norm_exp_I_mul_ofReal_sub_one (2 * Real.pi * (μ - φ))
    have hcomm : Complex.exp (((2 * Real.pi * (μ - φ) : ℝ) : ℂ) * Complex.I) =
        Complex.exp (Complex.I * ((2 * Real.pi * (μ - φ) : ℝ) : ℂ)) := by congr 1; ring
    rw [hcomm,
      show (1 : ℂ) - Complex.exp (Complex.I * ((2 * Real.pi * (μ - φ) : ℝ) : ℂ)) =
        -(Complex.exp (Complex.I * ((2 * Real.pi * (μ - φ) : ℝ) : ℂ)) - 1) by ring,
      norm_neg, hchord]
    rw [show (2 * Real.pi * (μ - φ)) / 2 = Real.pi * (μ - φ) from by ring,
      Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have harg : |Real.pi * (μ - φ)| ≤ Real.pi / 2 := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      nlinarith [Real.pi_pos, htle]
    have hsinle : 2 / Real.pi * |Real.pi * (μ - φ)| ≤ |Real.sin (Real.pi * (μ - φ))| :=
      Real.mul_abs_le_abs_sin harg
    have hval : 4 * |μ - φ| = 2 * (2 / Real.pi * |Real.pi * (μ - φ)|) := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      field_simp
      ring
    linarith [hsinle]
  have hsum : ‖bhmt_phase_estimation_theorem11_expSum M (μ - φ)‖ ≤ 1 / (2 * |μ - φ|) := by
    rw [hgeo, norm_div, div_le_iff₀ hdenpos]
    have h2 : (2 : ℝ) ≤ (1 / (2 * |μ - φ|)) *
        ‖1 - Complex.exp (((2 * Real.pi * (μ - φ) : ℝ) : ℂ) * Complex.I)‖ := by
      rw [one_div, inv_mul_eq_div, le_div_iff₀ (by positivity)]
      nlinarith [hden]
    linarith [hnum, h2]
  have hnorm : ‖momentumInnerAt M φ μ‖ =
      ((M : ℝ))⁻¹ * ‖bhmt_phase_estimation_theorem11_expSum M (μ - φ)‖ := by
    rw [momentumInnerAt_eq, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    ‖momentumInnerAt M φ μ‖ =
        ((M : ℝ))⁻¹ * ‖bhmt_phase_estimation_theorem11_expSum M (μ - φ)‖ := hnorm
    _ ≤ ((M : ℝ))⁻¹ * (1 / (2 * |μ - φ|)) := by
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1 / (2 * (M : ℝ) * |φ - μ|) := by
      rw [show |μ - φ| = |φ - μ| from abs_sub_comm μ φ, one_div, one_div, ← mul_inv_rev]
      congr 1
      ring

theorem momentumInner_norm_le (k : ℕ) (φ μ : ℝ)
    (hne : φ ≠ μ) (hsmall : |φ - μ| ≤ 1 / 2) :
    ‖momentumInner k φ μ‖ ≤ 1 / ((2 : ℝ) ^ (k + 1) * |φ - μ|) := by
  have h := momentumInnerAt_norm_le (2 ^ k) (by positivity) φ μ hne hsmall
  have heq : (2 : ℝ) * ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ (k + 1) := by
    push_cast; ring
  rw [momentumInner_eq_at]
  calc
    ‖momentumInnerAt (2 ^ k) φ μ‖ ≤ 1 / (2 * ((2 ^ k : ℕ) : ℝ) * |φ - μ|) := h
    _ = 1 / ((2 : ℝ) ^ (k + 1) * |φ - μ|) := by rw [heq]

theorem momentumInnerAt_pow_ge_half (M η : ℕ) (hη : 0 < η) (hM : 0 < M) (φ μ : ℝ)
    (h : |φ - μ| ≤ ((M : ℝ))⁻¹ / (2 * Real.pi * Real.sqrt (η : ℝ))) :
    ‖momentumInnerAt M φ μ‖ ^ η ≥ 1 / 2 := by
  have hMreal : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hηreal : (0 : ℝ) < (η : ℝ) := by exact_mod_cast hη
  have htbound : |μ - φ| ≤ ((M : ℝ))⁻¹ / (2 * Real.pi * Real.sqrt (η : ℝ)) := by
    rw [abs_sub_comm]; exact h

  have hre_eq : (momentumInnerAt M φ μ).re =
      ((M : ℝ))⁻¹ * ∑ y : Fin M, Real.cos (2 * Real.pi * (μ - φ) * (y.val : ℝ)) := by
    rw [momentumInnerAt_eq, ← Complex.ofReal_natCast, ← Complex.ofReal_inv (M : ℝ),
      Complex.re_ofReal_mul, bhmt_phase_estimation_theorem11_expSum, Complex.re_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro y _
    rw [Complex.exp_ofReal_mul_I_re]

  have hpoint : ∀ y : Fin M,
      1 - 1 / (2 * (η : ℝ)) ≤ Real.cos (2 * Real.pi * (μ - φ) * (y.val : ℝ)) := by
    intro y
    have hxn : 2 * Real.pi * |μ - φ| * (y.val : ℝ) ≤ 1 / Real.sqrt (η : ℝ) := by
      have hMposR : (0 : ℝ) < 2 * Real.pi * (M : ℝ) := by positivity
      have hmul2 := mul_le_mul_of_nonneg_left htbound hMposR.le
      have hfin : 2 * Real.pi * (M : ℝ) *
          (((M : ℝ))⁻¹ / (2 * Real.pi * Real.sqrt (η : ℝ))) = 1 / Real.sqrt (η : ℝ) := by
        field_simp
      have hMbound : 2 * Real.pi * |μ - φ| * (M : ℝ) ≤ 1 / Real.sqrt (η : ℝ) := by
        calc
          2 * Real.pi * |μ - φ| * (M : ℝ) = 2 * Real.pi * (M : ℝ) * |μ - φ| := by ring
          _ ≤ 2 * Real.pi * (M : ℝ) *
              (((M : ℝ))⁻¹ / (2 * Real.pi * Real.sqrt (η : ℝ))) := hmul2
          _ = 1 / Real.sqrt (η : ℝ) := hfin
      have hleM : 2 * Real.pi * |μ - φ| * (y.val : ℝ) ≤ 2 * Real.pi * |μ - φ| * (M : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact_mod_cast le_of_lt y.isLt
      linarith [hleM, hMbound]
    have hx2 : (2 * Real.pi * (μ - φ) * (y.val : ℝ)) ^ 2 ≤ 1 / (η : ℝ) := by
      have habs : |2 * Real.pi * (μ - φ) * (y.val : ℝ)| ≤ 1 / Real.sqrt (η : ℝ) := by
        have hh : |2 * Real.pi * (μ - φ) * (y.val : ℝ)| = 2 * Real.pi * |μ - φ| * (y.val : ℝ) := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos,
            abs_of_pos (by norm_num : (0 : ℝ) < 2),
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ (y.val : ℝ))]
        rw [hh]; exact hxn
      have hp := pow_le_pow_left₀ (abs_nonneg (2 * Real.pi * (μ - φ) * (y.val : ℝ))) habs 2
      rw [sq_abs, one_div, inv_pow, Real.sq_sqrt hηreal.le] at hp
      simpa [one_div] using hp
    have hcos := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * (μ - φ) * (y.val : ℝ))
    have hhalf : (1 : ℝ) / (2 * (η : ℝ)) = (1 / (η : ℝ)) / 2 := by
      field_simp
    nlinarith [hx2, hcos, hηreal, hhalf]
  have hre : 1 - 1 / (2 * (η : ℝ)) ≤ (momentumInnerAt M φ μ).re := by
    rw [hre_eq]
    have hsum : (M : ℝ) * (1 - 1 / (2 * (η : ℝ))) ≤
        ∑ y : Fin M, Real.cos (2 * Real.pi * (μ - φ) * (y.val : ℝ)) := by
      have hc := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin M)))
        (fun y (_ : y ∈ (Finset.univ : Finset (Fin M))) => hpoint y)
      have hconst : (∑ _ : Fin M, (1 - 1 / (2 * (η : ℝ)))) =
          (M : ℝ) * (1 - 1 / (2 * (η : ℝ))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [hconst] at hc
      exact hc
    calc
      1 - 1 / (2 * (η : ℝ)) = ((M : ℝ))⁻¹ * ((M : ℝ) * (1 - 1 / (2 * (η : ℝ)))) := by
        rw [← mul_assoc, inv_mul_cancel₀ hMreal.ne', one_mul]
      _ ≤ ((M : ℝ))⁻¹ * ∑ y : Fin M, Real.cos (2 * Real.pi * (μ - φ) * (y.val : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hsum (by positivity)
  have hnonneg : (0 : ℝ) ≤ 1 - 1 / (2 * (η : ℝ)) := by
    have h1 : (1 : ℝ) ≤ (η : ℝ) := by exact_mod_cast hη
    have hle : 1 / (2 * (η : ℝ)) ≤ 1 / 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      nlinarith
    linarith
  have hnorm : 1 - 1 / (2 * (η : ℝ)) ≤ ‖momentumInnerAt M φ μ‖ :=
    le_trans hre (Complex.re_le_norm _)
  have hmono : (1 - 1 / (2 * (η : ℝ))) ^ η ≤ ‖momentumInnerAt M φ μ‖ ^ η :=
    pow_le_pow_left₀ hnonneg hnorm η
  have hbern : (1 / 2 : ℝ) ≤ (1 - 1 / (2 * (η : ℝ))) ^ η := by
    have hcond : (-2 : ℝ) ≤ -(1 / (2 * (η : ℝ))) := by
      have h1 : (1 : ℝ) ≤ (η : ℝ) := by exact_mod_cast hη
      have hle : 1 / (2 * (η : ℝ)) ≤ 2 := by
        have hle2 : 1 / (2 * (η : ℝ)) ≤ 1 / 2 := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          nlinarith
        linarith
      linarith
    have hb := one_add_mul_le_pow (a := -(1 / (2 * (η : ℝ)))) hcond η
    have hcast : (η : ℝ) * -(1 / (2 * (η : ℝ))) = -(1 / 2) := by
      have hne : (η : ℝ) ≠ 0 := hηreal.ne'
      field_simp
    rw [hcast] at hb
    have hleft : (1 : ℝ) + -(1 / 2) = 1 / 2 := by norm_num
    have hright : (1 : ℝ) + -(1 / (2 * (η : ℝ))) = 1 - 1 / (2 * (η : ℝ)) := by ring
    rw [hleft, hright] at hb
    exact hb
  exact le_trans hbern hmono

theorem momentumInner_pow_ge_half (k η : ℕ) (hη : 0 < η) (φ μ : ℝ)
    (h : |φ - μ| ≤ ((2 : ℕ) ^ k : ℝ)⁻¹ / (2 * Real.pi * Real.sqrt (η : ℝ))) :
    ‖momentumInner k φ μ‖ ^ η ≥ 1 / 2 := by
  rw [momentumInner_eq_at]
  exact momentumInnerAt_pow_ge_half (2 ^ k) η hη (by positivity) φ μ (by simpa using h)

theorem appendixC_momentum_bounds (k η : ℕ) (hη : 0 < η) (φ μ : ℝ) :
    (φ ≠ μ → |φ - μ| ≤ 1 / 2 →
      ‖momentumInner k φ μ‖ ≤ 1 / ((2 : ℝ) ^ (k + 1) * |φ - μ|)) ∧
    (|φ - μ| ≤ ((2 : ℕ) ^ k : ℝ)⁻¹ / (2 * Real.pi * Real.sqrt (η : ℝ)) →
      ‖momentumInner k φ μ‖ ^ η ≥ 1 / 2) := by
  refine ⟨fun hne hsmall => momentumInner_norm_le k φ μ hne hsmall, ?_⟩
  intro h
  exact momentumInner_pow_ge_half k η hη φ μ h

end Qatlib.Papers.GroundState08.MainResults.MomentumInnerProduct
