/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AndersonLoc09.MainResults.MinimalGap
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AndersonLoc09.MainResults

open Real

theorem gap_ultra_small (N0 v : ℝ) (hN0 : 0 < N0) (hv : 0 < v) :
    ∃ N1 : ℝ, 0 < N1 ∧ ∀ N : ℝ, N1 ≤ N →
      gapFormula (v * N) N N0 ≤ Real.exp (-N) := by
  refine ⟨N0 * Real.exp (8 / v), by positivity, ?_⟩
  intro N hN
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity) hN
  unfold gapFormula
  rw [Real.exp_le_exp]
  have hratio : Real.exp (8 / v) ≤ N / N0 := by
    rw [le_div_iff₀ hN0]
    simpa only [mul_comm] using hN
  have hlog : 8 / v ≤ Real.log (N / N0) := by
    have h := Real.log_le_log (Real.exp_pos (8 / v)) hratio
    rwa [Real.log_exp] at h
  have hcoef : 0 ≤ v * N / 8 := by positivity
  have hmul : (v * N / 8) * (8 / v) ≤ (v * N / 8) * Real.log (N / N0) :=
    mul_le_mul_of_nonneg_left hlog hcoef
  have hsimp : (v * N / 8) * (8 / v) = N := by
    field_simp
  rw [hsimp] at hmul
  linarith

theorem aqo_runtime_exceeds_exp (N0 v N : ℝ) (hN0 : 0 < N0) (hv : 0 < v) (hN : 0 < N)
    (hgap : gapFormula (v * N) N N0 ≤ Real.exp (-N)) :
    Real.exp N ≤ 1 / (gapFormula (v * N) N N0) ^ 2 := by
  have hgp : 0 < gapFormula (v * N) N N0 := by
    unfold gapFormula
    positivity
  have hsq : (gapFormula (v * N) N N0) ^ 2 ≤ (Real.exp (-N)) ^ 2 :=
    pow_le_pow_left₀ (le_of_lt hgp) hgap 2
  have hrhs : (Real.exp (-N)) ^ 2 = Real.exp (-2 * N) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hrhs] at hsq
  have hx : 1 / Real.exp (-2 * N) = Real.exp (2 * N) := by
    rw [one_div, ← Real.exp_neg]
    congr 1
    ring
  have hinv : 1 / Real.exp (-2 * N) ≤ 1 / (gapFormula (v * N) N N0) ^ 2 :=
    one_div_le_one_div_of_le (pow_pos hgp 2) hsq
  calc Real.exp N ≤ Real.exp (2 * N) := Real.exp_le_exp.mpr (by linarith)
    _ = 1 / Real.exp (-2 * N) := hx.symm
    _ ≤ 1 / (gapFormula (v * N) N N0) ^ 2 := hinv

theorem aqo_minimal_gap_super_exponential (N0 v : ℝ) (hN0 : 0 < N0) (hv : 0 < v) :
    ∃ N1 : ℝ, 0 < N1 ∧ ∀ N : ℝ, N1 ≤ N →
      gapFormula (v * N) N N0 ≤ Real.exp (-N) ∧
      Real.exp N ≤ 1 / (gapFormula (v * N) N N0) ^ 2 := by
  obtain ⟨N1, hN1, hbound⟩ := gap_ultra_small N0 v hN0 hv
  refine ⟨N1, hN1, ?_⟩
  intro N hNN
  have hNpos : 0 < N := lt_of_lt_of_le hN1 hNN
  exact ⟨hbound N hNN, aqo_runtime_exceeds_exp N0 v N hN0 hv hNpos (hbound N hNN)⟩

end Qatlib.Papers.AndersonLoc09.MainResults
