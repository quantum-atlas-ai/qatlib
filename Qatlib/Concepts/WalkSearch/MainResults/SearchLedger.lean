/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MainResults.PhaseGap
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Qatlib.Concepts.WalkSearch.MainResults.SearchLedger

open Qatlib.Concepts.WalkSearch.MainResults.PhaseGap

theorem fiveSample_failure_lt_quarter : ((3 : ℝ) / 4) ^ 5 < 1 / 4 := by
  norm_num

def searchWalkCalls (T k s : ℕ) : ℝ := (T : ℝ) * ((k : ℝ) * (2 : ℝ) ^ (s + 1))

theorem search_calls_le {ε δ Δ : ℝ} {T k s : ℕ}
    (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) (hδ : 0 < δ)
    (hT : (T : ℝ) ≤ 1 / Real.sqrt ε)
    (hgap : 2 * Real.sqrt δ ≤ Δ)
    (hcopies : (2 : ℝ) ^ (s + 1) ≤ 8 * Real.pi / Δ)
    (hk : (k : ℝ) ≤ Real.logb 2 (1 / Real.sqrt ε) + 1) :
    searchWalkCalls T k s ≤
      16 * Real.pi * (1 / Real.sqrt ε) *
        ((1 / Real.sqrt δ) * Real.log (1 / Real.sqrt ε)) := by
  have hy_pos : 0 < 1 / Real.sqrt ε := by positivity
  have hy2 : 2 ≤ 1 / Real.sqrt ε := by
    have hs : Real.sqrt ε ≤ 1 / 2 := by
      have h := Real.sqrt_le_sqrt hε4
      norm_num at h ⊢
      exact h
    rw [le_div_iff₀ (Real.sqrt_pos.mpr hε)]
    nlinarith only [hs, Real.sqrt_nonneg ε]
  have hly : (0.6931471803 : ℝ) ≤ Real.log (1 / Real.sqrt ε) :=
    le_trans Real.log_two_gt_d9.le (Real.log_le_log (by norm_num) hy2)
  have hlog2pos : 0 < Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hdiv : Real.log (1 / Real.sqrt ε) / Real.log 2 ≤
      2 * Real.log (1 / Real.sqrt ε) := by
    rw [div_le_iff₀ hlog2pos]
    nlinarith only [hly, Real.log_two_gt_d9]
  have hone : (1 : ℝ) ≤ 2 * Real.log (1 / Real.sqrt ε) := by linarith only [hly]
  have hk4 : (k : ℝ) ≤ 4 * Real.log (1 / Real.sqrt ε) := by
    have hlogb : Real.logb 2 (1 / Real.sqrt ε) =
        Real.log (1 / Real.sqrt ε) / Real.log 2 := rfl
    rw [hlogb] at hk
    linarith only [hk, hdiv, hone]
  have hsδ : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hc8 : 8 * Real.pi / Δ ≤ 4 * Real.pi / Real.sqrt δ := by
    rw [div_le_div_iff₀ (by linarith : 0 < Δ) hsδ]
    nlinarith only [hgap, Real.pi_pos]
  have h1 : (k : ℝ) * (2 : ℝ) ^ (s + 1) ≤
      (4 * Real.log (1 / Real.sqrt ε)) * (8 * Real.pi / Δ) :=
    mul_le_mul hk4 hcopies (by positivity) (by positivity)
  have h2 : (4 * Real.log (1 / Real.sqrt ε)) * (8 * Real.pi / Δ) ≤
      (4 * Real.log (1 / Real.sqrt ε)) * (4 * Real.pi / Real.sqrt δ) :=
    mul_le_mul_of_nonneg_left hc8 (by positivity)
  have h3 : (T : ℝ) * ((k : ℝ) * (2 : ℝ) ^ (s + 1)) ≤
      (1 / Real.sqrt ε) * ((4 * Real.log (1 / Real.sqrt ε)) *
        (4 * Real.pi / Real.sqrt δ)) :=
    mul_le_mul hT (le_trans h1 h2) (by positivity) hy_pos.le
  have h4 : (1 / Real.sqrt ε) * ((4 * Real.log (1 / Real.sqrt ε)) *
        (4 * Real.pi / Real.sqrt δ)) =
      16 * Real.pi * (1 / Real.sqrt ε) *
        ((1 / Real.sqrt δ) * Real.log (1 / Real.sqrt ε)) := by ring
  calc
    searchWalkCalls T k s = (T : ℝ) * ((k : ℝ) * (2 : ℝ) ^ (s + 1)) := rfl
    _ ≤ _ := h3
    _ = _ := h4

def searchTotalCost (S U C : ℝ) (T k s : ℕ) : ℝ :=
  5 * (S + C) + searchWalkCalls T k s * U + C

theorem search_total_cost_le {ε δ Δ : ℝ} {T k s : ℕ} {S U C : ℝ}
    (hS : 0 ≤ S) (hU : 0 ≤ U) (hC : 0 ≤ C)
    (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) (hδ : 0 < δ)
    (hT : (T : ℝ) ≤ 1 / Real.sqrt ε)
    (hgap : 2 * Real.sqrt δ ≤ Δ)
    (hcopies : (2 : ℝ) ^ (s + 1) ≤ 8 * Real.pi / Δ)
    (hk : (k : ℝ) ≤ Real.logb 2 (1 / Real.sqrt ε) + 1) :
    searchTotalCost S U C T k s ≤
      (16 * Real.pi + 6) *
        (S + (1 / Real.sqrt ε) *
          ((1 / Real.sqrt δ) * Real.log (1 / Real.sqrt ε) * U + C)) := by
  have hy_pos : 0 < 1 / Real.sqrt ε := by positivity
  have hy2 : 2 ≤ 1 / Real.sqrt ε := by
    have hs : Real.sqrt ε ≤ 1 / 2 := by
      have h := Real.sqrt_le_sqrt hε4
      norm_num at h ⊢
      exact h
    rw [le_div_iff₀ (Real.sqrt_pos.mpr hε)]
    nlinarith only [hs, Real.sqrt_nonneg ε]
  have hcalls := search_calls_le hε hε4 hδ hT hgap hcopies hk
  have hp := Real.pi_pos
  set L := Real.log (1 / Real.sqrt ε) with hL
  set D := (1 / Real.sqrt δ) * L with hD
  have hDL : 0 ≤ D := by
    rw [hD]
    exact mul_nonneg (by positivity) (by
      apply Real.log_nonneg
      have hs : Real.sqrt ε ≤ 1 / 2 := by
        have h := Real.sqrt_le_sqrt hε4
        norm_num at h ⊢
        exact h
      rw [le_div_iff₀ (Real.sqrt_pos.mpr hε)]
      nlinarith only [hs, Real.sqrt_nonneg ε])
  have hcallsD : searchWalkCalls T k s ≤ 16 * Real.pi * (1 / Real.sqrt ε) * D := by
    rw [hD, hL]
    exact hcalls
  have hmain : searchWalkCalls T k s * U ≤
      (16 * Real.pi + 6) * ((1 / Real.sqrt ε) * (D * U)) := by
    have h1 : searchWalkCalls T k s * U ≤
        (16 * Real.pi * (1 / Real.sqrt ε) * D) * U :=
      mul_le_mul_of_nonneg_right hcallsD hU
    have hKl : 16 * Real.pi ≤ 16 * Real.pi + 6 := by linarith
    have h2 : (16 * Real.pi * (1 / Real.sqrt ε) * D) * U ≤
        ((16 * Real.pi + 6) * (1 / Real.sqrt ε) * D) * U := by
      apply mul_le_mul_of_nonneg_right _ hU
      nlinarith only [hKl, hy_pos, hDL]
    have h3 : ((16 * Real.pi + 6) * (1 / Real.sqrt ε) * D) * U =
        (16 * Real.pi + 6) * ((1 / Real.sqrt ε) * (D * U)) := by ring
    linarith only [h1, h2, h3]
  have hSC : 5 * (S + C) + C ≤
      (16 * Real.pi + 6) * S + (16 * Real.pi + 6) * ((1 / Real.sqrt ε) * C) := by
    have h1 : 5 * S ≤ (16 * Real.pi + 6) * S :=
      mul_le_mul_of_nonneg_right (by linarith only [hp]) hS
    have hK : (5 : ℝ) * 1 + 1 ≤ (16 * Real.pi + 6) * (1 / Real.sqrt ε) := by
      nlinarith only [hp, hy2]
    have h2 : 6 * C ≤ (16 * Real.pi + 6) * ((1 / Real.sqrt ε) * C) := by
      have hK6 : (6 : ℝ) ≤ (16 * Real.pi + 6) * (1 / Real.sqrt ε) := by linarith only [hK]
      calc 6 * C = 6 * C := rfl
        _ ≤ ((16 * Real.pi + 6) * (1 / Real.sqrt ε)) * C :=
            mul_le_mul_of_nonneg_right hK6 hC
        _ = (16 * Real.pi + 6) * ((1 / Real.sqrt ε) * C) := by ring
    calc 5 * (S + C) + C = 5 * S + 6 * C := by ring
      _ ≤ (16 * Real.pi + 6) * S + (16 * Real.pi + 6) * ((1 / Real.sqrt ε) * C) :=
          add_le_add h1 h2
  rw [searchTotalCost]
  have hEq : (16 * Real.pi + 6) * S +
        (16 * Real.pi + 6) * ((1 / Real.sqrt ε) * C) +
        (16 * Real.pi + 6) * ((1 / Real.sqrt ε) * (D * U)) =
      (16 * Real.pi + 6) *
        (S + (1 / Real.sqrt ε) * (D * U + C)) := by ring
  have := add_le_add hSC hmain
  linarith only [this, hEq]

def searchWalkCallsLogFree (T s : ℕ) : ℝ := (T : ℝ) * (2 : ℝ) ^ (s + 1)

theorem search_calls_logfree_le {ε δ Δ : ℝ} {T s : ℕ}
    (hε : 0 < ε) (hδ : 0 < δ)
    (hT : (T : ℝ) ≤ 1 / Real.sqrt ε)
    (hgap : 2 * Real.sqrt δ ≤ Δ)
    (hcopies : (2 : ℝ) ^ (s + 1) ≤ 8 * Real.pi / Δ) :
    searchWalkCallsLogFree T s ≤
      4 * Real.pi * (1 / Real.sqrt ε) * (1 / Real.sqrt δ) := by
  have hy_pos : 0 < 1 / Real.sqrt ε := by positivity
  have hsδ : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hc8 : 8 * Real.pi / Δ ≤ 4 * Real.pi / Real.sqrt δ := by
    rw [div_le_div_iff₀ (by linarith : 0 < Δ) hsδ]
    nlinarith only [hgap, Real.pi_pos]
  have h1 : (1 / Real.sqrt ε) * (8 * Real.pi / Δ) ≤
      (1 / Real.sqrt ε) * (4 * Real.pi / Real.sqrt δ) :=
    mul_le_mul_of_nonneg_left hc8 hy_pos.le
  have h3 : (T : ℝ) * (2 : ℝ) ^ (s + 1) ≤
      (1 / Real.sqrt ε) * (4 * Real.pi / Real.sqrt δ) :=
    le_trans (mul_le_mul hT hcopies (by positivity) hy_pos.le)
      (by linarith only [h1])
  calc
    searchWalkCallsLogFree T s = (T : ℝ) * (2 : ℝ) ^ (s + 1) := rfl
    _ ≤ _ := h3
    _ = 4 * Real.pi * (1 / Real.sqrt ε) * (1 / Real.sqrt δ) := by ring

def searchTotalCostLogFree (S U C : ℝ) (T s : ℕ) : ℝ :=
  5 * (S + C) + searchWalkCallsLogFree T s * U + C

theorem search_total_cost_logfree_le {ε δ Δ : ℝ} {T s : ℕ} {S U C : ℝ}
    (hS : 0 ≤ S) (hU : 0 ≤ U) (hC : 0 ≤ C)
    (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) (hδ : 0 < δ)
    (hT : (T : ℝ) ≤ 1 / Real.sqrt ε)
    (hgap : 2 * Real.sqrt δ ≤ Δ)
    (hcopies : (2 : ℝ) ^ (s + 1) ≤ 8 * Real.pi / Δ) :
    searchTotalCostLogFree S U C T s ≤
      (4 * Real.pi + 6) *
        (S + (1 / Real.sqrt ε) * ((1 / Real.sqrt δ) * U + C)) := by
  have hy_pos : 0 < 1 / Real.sqrt ε := by positivity
  have hy2 : 2 ≤ 1 / Real.sqrt ε := by
    have hs : Real.sqrt ε ≤ 1 / 2 := by
      have h := Real.sqrt_le_sqrt hε4
      norm_num at h ⊢
      exact h
    rw [le_div_iff₀ (Real.sqrt_pos.mpr hε)]
    nlinarith only [hs, Real.sqrt_nonneg ε]
  have hcalls := search_calls_logfree_le hε hδ hT hgap hcopies
  have hp := Real.pi_pos
  have hcallsU : searchWalkCallsLogFree T s * U ≤
      (4 * Real.pi + 6) * ((1 / Real.sqrt ε) * ((1 / Real.sqrt δ) * U)) := by
    have h1 : searchWalkCallsLogFree T s * U ≤
        (4 * Real.pi * (1 / Real.sqrt ε) * (1 / Real.sqrt δ)) * U :=
      mul_le_mul_of_nonneg_right hcalls hU
    have h2 : (4 * Real.pi * (1 / Real.sqrt ε) * (1 / Real.sqrt δ)) * U ≤
        ((4 * Real.pi + 6) * (1 / Real.sqrt ε) * (1 / Real.sqrt δ)) * U := by
      apply mul_le_mul_of_nonneg_right _ hU
      have hsδ : 0 ≤ 1 / Real.sqrt δ := by positivity
      nlinarith only [hp, hy_pos, hsδ]
    have h3 : ((4 * Real.pi + 6) * (1 / Real.sqrt ε) * (1 / Real.sqrt δ)) * U =
        (4 * Real.pi + 6) * ((1 / Real.sqrt ε) * ((1 / Real.sqrt δ) * U)) := by ring
    linarith only [h1, h2, h3]
  have hSC : 5 * (S + C) + C ≤
      (4 * Real.pi + 6) * S + (4 * Real.pi + 6) * ((1 / Real.sqrt ε) * C) := by
    have h1 : 5 * S ≤ (4 * Real.pi + 6) * S :=
      mul_le_mul_of_nonneg_right (by linarith only [hp]) hS
    have hK6 : (6 : ℝ) ≤ (4 * Real.pi + 6) * (1 / Real.sqrt ε) := by
      nlinarith only [hp, hy2]
    have h2 : 6 * C ≤ (4 * Real.pi + 6) * ((1 / Real.sqrt ε) * C) := by
      calc 6 * C = 6 * C := rfl
        _ ≤ ((4 * Real.pi + 6) * (1 / Real.sqrt ε)) * C :=
            mul_le_mul_of_nonneg_right hK6 hC
        _ = (4 * Real.pi + 6) * ((1 / Real.sqrt ε) * C) := by ring
    calc 5 * (S + C) + C = 5 * S + 6 * C := by ring
      _ ≤ (4 * Real.pi + 6) * S + (4 * Real.pi + 6) * ((1 / Real.sqrt ε) * C) :=
          add_le_add h1 h2
  rw [searchTotalCostLogFree]
  have hEq : (4 * Real.pi + 6) * S +
        (4 * Real.pi + 6) * ((1 / Real.sqrt ε) * C) +
        (4 * Real.pi + 6) * ((1 / Real.sqrt ε) * ((1 / Real.sqrt δ) * U)) =
      (4 * Real.pi + 6) *
        (S + (1 / Real.sqrt ε) * ((1 / Real.sqrt δ) * U + C)) := by ring
  have := add_le_add hSC hcallsU
  linarith only [this, hEq]

theorem singularPhaseGap_ge_two_sqrt_gap {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    2 * Real.sqrt δ ≤ phaseGap (1 - δ) :=
  phaseGap_ge_two_sqrt_gap hδ0 hδ1

end Qatlib.Concepts.WalkSearch.MainResults.SearchLedger
