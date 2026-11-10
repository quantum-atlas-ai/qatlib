/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.OrderedList07.MainResults

lemma stage_count_increment (L I : ℝ) (hL : 2 / 3 ≤ L) (hI : 0 < I) :
    L / (I * (1 - 1 / (3 * L))) ≤ L / I + 2 / (3 * I) := by
  have hL0 : 0 < L := by linarith
  have h3L : 0 < 3 * L := by positivity
  have hI3 : (3 : ℝ) * I ≠ 0 := by positivity
  have hIn : I ≠ 0 := hI.ne'
  have hL3 : (3 : ℝ) * L - 1 ≠ 0 := by
    have : (1 : ℝ) < 3 * L := by linarith
    linarith
  have hden : 0 < 1 - 1 / (3 * L) := by
    have hlt : 1 / (3 * L) < 1 := by
      rw [div_lt_one h3L]
      linarith
    linarith
  have hdenpos : 0 < I * (1 - 1 / (3 * L)) := mul_pos hI hden
  rw [div_le_iff₀ hdenpos]
  have hrhs : (L / I + 2 / (3 * I)) * (I * (1 - 1 / (3 * L)))
      = (L + 2 / 3) * (1 - 1 / (3 * L)) := by
    field_simp
  rw [hrhs]
  have hstep : (L + 2 / 3) * (1 - 1 / (3 * L))
      = ((L + 2 / 3) * (3 * L - 1)) / (3 * L) := by
    field_simp
  rw [hstep, le_div_iff₀ h3L]
  nlinarith

lemma entropy_gap_le (L ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    L - Real.log (1 / ε) / Real.log 2 ≤ L := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hge : 0 ≤ Real.log (1 / ε) / Real.log 2 := by
    apply div_nonneg _ h2.le
    apply Real.log_nonneg
    rw [le_div_iff₀ hε0]
    linarith
  linarith

lemma stage_count_entropy_gap (L I ε : ℝ) (hL : 2 / 3 ≤ L) (hI : 0 < I)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (L - Real.log (1 / ε) / Real.log 2) / (I * (1 - 1 / (3 * L)))
      ≤ L / I + 2 / (3 * I) := by
  have hL0 : 0 < L := by linarith
  have hden : 0 < 1 - 1 / (3 * L) := by
    have hlt : 1 / (3 * L) < 1 := by
      rw [div_lt_one (by positivity : (0 : ℝ) < 3 * L)]
      linarith
    linarith
  have hdenpos : 0 < I * (1 - 1 / (3 * L)) := mul_pos hI hden
  have hgap := entropy_gap_le L ε hε0 hε1
  calc
    (L - Real.log (1 / ε) / Real.log 2) / (I * (1 - 1 / (3 * L)))
        ≤ L / (I * (1 - 1 / (3 * L))) :=
          div_le_div_of_nonneg_right hgap hdenpos.le
    _ ≤ L / I + 2 / (3 * I) := stage_count_increment L I hL hI

lemma window_card_le (i l : ℕ) :
    (Finset.Icc (i - l) (i + l)).card ≤ 2 * l + 1 := by
  have h : (Finset.Icc (i - l) (i + l)).card = (i + l) + 1 - (i - l) :=
    Nat.card_Icc (i - l) (i + l)
  omega

lemma window_depth_le (w : ℕ) (_hw : 0 < w) :
    w ≤ 2 ^ (Nat.log 2 w + 1) := by
  have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) w
  simpa [Nat.succ_eq_add_one] using le_of_lt h

lemma theorem11_branch_exhaustive (L δ : ℝ) : δ ≤ L ^ 3 ∨ L ^ 3 ≤ δ :=
  le_total δ (L ^ 3)

lemma theorem11_second_branch_envelope (L I δ δ' c₁ : ℝ) (hL1 : 1 ≤ L) (hI : 0 < I)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδ' : 0 < δ') (hδδ' : δ ≤ δ') (hc₁ : 0 ≤ c₁) :
    L / I + c₁ * (Real.log L / Real.log 2) * (Real.log (1 / δ') / Real.log 2) / I
        + 2 / (3 * I) + (Real.log (1 / δ) / Real.log 2) / I
      ≤ L / I + (c₁ * (Real.log L / Real.log 2) + 1)
          * (Real.log (1 / δ) / Real.log 2) / I + 2 / (3 * I) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogmono : Real.log (1 / δ') ≤ Real.log (1 / δ) := by
    apply Real.log_le_log (by positivity)
    rw [div_le_div_iff₀ hδ' hδ]
    linarith
  have hlogδ : 0 ≤ Real.log (1 / δ) / Real.log 2 := by
    apply div_nonneg _ h2.le
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ]
    linarith
  have hlogδ' : Real.log (1 / δ') / Real.log 2 ≤ Real.log (1 / δ) / Real.log 2 :=
    div_le_div_of_nonneg_right hlogmono h2.le
  have hrearr : L / I + (c₁ * (Real.log L / Real.log 2) + 1)
        * (Real.log (1 / δ) / Real.log 2) / I + 2 / (3 * I)
      = L / I + c₁ * (Real.log L / Real.log 2) * (Real.log (1 / δ) / Real.log 2) / I
        + (Real.log (1 / δ) / Real.log 2) / I + 2 / (3 * I) := by
    field_simp
    try ring
  rw [hrearr]
  have hLlog : 0 ≤ Real.log L / Real.log 2 := by
    apply div_nonneg _ h2.le
    exact Real.log_nonneg hL1
  have hstep : c₁ * (Real.log L / Real.log 2) * (Real.log (1 / δ') / Real.log 2) / I
      ≤ c₁ * (Real.log L / Real.log 2) * (Real.log (1 / δ) / Real.log 2) / I := by
    apply div_le_div_of_nonneg_right _ hI.le
    exact mul_le_mul_of_nonneg_left hlogδ' (mul_nonneg hc₁ hLlog)
  linarith

end Qatlib.Papers.OrderedList07.MainResults
