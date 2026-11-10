/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ClawFinding07.MainResults.QueryBound.KClawDetect
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ClawFinding07.MainResults.QueryBound

open scoped BigOperators

theorem two_runs_error {s : ℕ} :
    2 * (1 / 3 : ℝ) ^ (s + 2) < (1 / 3 : ℝ) ^ (s + 1) := by
  have hpow : (1 / 3 : ℝ) ^ (s + 2) = (1 / 3 : ℝ) ^ (s + 1) * (1 / 3) := by
    rw [pow_succ]
  have hpos : (0 : ℝ) < (1 / 3 : ℝ) ^ (s + 1) := by positivity
  rw [hpow]
  nlinarith

theorem stage_error_lt_sixth (S : ℕ) :
    ∑ s ∈ Finset.range S, (1 / 3 : ℝ) ^ (s + 2) < 1 / 6 := by

  have hform : ∀ S : ℕ,
      ∑ s ∈ Finset.range S, (1 / 3 : ℝ) ^ (s + 2)
        = (1 / 6) * (1 - (1 / 3 : ℝ) ^ S) := by
    intro S
    induction S with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih, pow_succ]
        ring
  rw [hform]
  have hpos : (0 : ℝ) < (1 / 3 : ℝ) ^ S := by positivity
  nlinarith

theorem clawSearch_error_lt_third (S2 S3 : ℕ) :
    (∑ s ∈ Finset.range S2, (1 / 3 : ℝ) ^ (s + 2))
      + (∑ s ∈ Finset.range S3, (1 / 3 : ℝ) ^ (s + 2)) < 1 / 3 := by
  have h2 := stage_error_lt_sixth S2
  have h3 := stage_error_lt_sixth S3
  linarith

theorem weighted_geom_four_fifths (S : ℕ) :
    (∑ s ∈ Finset.range S, ((s : ℝ) + 1) * (4 / 5 : ℝ) ^ (s + 1))
      = 20 * (1 - ((S : ℝ) + 1) * (4 / 5 : ℝ) ^ S
                  + (S : ℝ) * (4 / 5 : ℝ) ^ (S + 1)) := by
  induction S with
  | zero => simp
  | succ S ih =>
      rw [Finset.sum_range_succ, ih]
      have h1 : (4 / 5 : ℝ) ^ (S + 1) = (4 / 5 : ℝ) ^ S * (4 / 5) := pow_succ _ _
      have h2 : (4 / 5 : ℝ) ^ (S + 2) = (4 / 5 : ℝ) ^ S * (4 / 5) * (4 / 5) := by
        rw [pow_succ, h1]
      rw [h1, h2]
      push_cast
      ring

theorem weighted_geom_four_fifths_le (S : ℕ) :
    (∑ s ∈ Finset.range S, ((s : ℝ) + 1) * (4 / 5 : ℝ) ^ (s + 1)) ≤ 20 := by
  rw [weighted_geom_four_fifths]
  have hq0 : (0 : ℝ) ≤ (4 / 5 : ℝ) ^ S := by positivity
  have hq : (4 / 5 : ℝ) ≤ 1 := by norm_num
  have hbracket : ((S : ℝ) + 1) * (4 / 5 : ℝ) ^ S
      - (S : ℝ) * (4 / 5 : ℝ) ^ (S + 1) ≥ 0 := by
    have hle : (S : ℝ) * (4 / 5 : ℝ) ^ (S + 1)
        ≤ ((S : ℝ) + 1) * (4 / 5 : ℝ) ^ S := by
      have hmul : (S : ℝ) * (4 / 5 : ℝ) ≤ ((S : ℝ) + 1) := by nlinarith
      have h := mul_le_mul_of_nonneg_right hmul hq0
      calc (S : ℝ) * (4 / 5 : ℝ) ^ (S + 1)
          = ((S : ℝ) * (4 / 5)) * (4 / 5 : ℝ) ^ S := by
            rw [pow_succ]
            ring
        _ ≤ ((S : ℝ) + 1) * (4 / 5 : ℝ) ^ S := h
    linarith
  nlinarith

theorem four_fifths_pow_cube (n : ℕ) :
    ((4 / 5 : ℝ) ^ n) ^ 3 = (64 / 125 : ℝ) ^ n := by
  rw [← pow_mul, show n * 3 = 3 * n by ring, pow_mul]
  norm_num

theorem four_fifths_pow_sq (n : ℕ) :
    ((4 / 5 : ℝ) ^ n) ^ 2 = (16 / 25 : ℝ) ^ n := by
  rw [← pow_mul, show n * 2 = 2 * n by ring, pow_mul]
  norm_num

theorem half_pow_le (n : ℕ) :
    (1 / 2 : ℝ) ^ n ≤ (64 / 125 : ℝ) ^ n :=
  pow_le_pow_left₀ (by norm_num) (by norm_num) n

theorem half_pow_le_sq (n : ℕ) : (1 / 2 : ℝ) ^ n ≤ ((4 / 5 : ℝ) ^ n) ^ 2 := by
  calc (1 / 2 : ℝ) ^ n ≤ (16 / 25 : ℝ) ^ n :=
        pow_le_pow_left₀ (by norm_num) (by norm_num) n
    _ = ((4 / 5 : ℝ) ^ n) ^ 2 := by rw [four_fifths_pow_sq]

theorem rpow_third_div_pow_le {N M : ℝ} (hN : 0 ≤ N) (hM : 0 ≤ M) (n : ℕ) :
    (N * (M / 2 ^ n)) ^ (1 / 3 : ℝ)
      ≤ (N * M) ^ (1 / 3 : ℝ) * (4 / 5 : ℝ) ^ n := by
  have hNM : 0 ≤ N * M := mul_nonneg hN hM
  have hbase : N * (M / 2 ^ n) = (N * M) * (1 / 2 : ℝ) ^ n := by
    rw [div_eq_mul_inv, ← inv_pow]
    norm_num
    ring
  have hle : N * (M / 2 ^ n) ≤ (N * M) * ((4 / 5 : ℝ) ^ n) ^ 3 := by
    rw [hbase, four_fifths_pow_cube]
    exact mul_le_mul_of_nonneg_left (half_pow_le n) hNM
  have hmain := Real.rpow_le_rpow (by positivity) hle (by norm_num : (0 : ℝ) ≤ 1 / 3)
  rw [hbase, Real.mul_rpow hNM (by positivity),
    Real.mul_rpow hNM (by positivity)] at hmain
  have hcube : ((((4 / 5 : ℝ) ^ n) ^ 3) ^ (1 / 3 : ℝ)) = (4 / 5 : ℝ) ^ n := by
    rw [show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num,
      Real.pow_rpow_inv_natCast (by positivity : (0 : ℝ) ≤ (4 / 5 : ℝ) ^ n)
        (by norm_num : (3 : ℕ) ≠ 0)]
  rw [hcube] at hmain
  rw [hbase, Real.mul_rpow hNM (by positivity)]
  exact hmain

theorem rpow_third_sq_div_pow_le {N : ℝ} (hN : 0 ≤ N) (n : ℕ) :
    ((N / 2 ^ n) * (N / 2 ^ n)) ^ (1 / 3 : ℝ)
      ≤ (N ^ 2) ^ (1 / 3 : ℝ) * (4 / 5 : ℝ) ^ n := by
  have hN2 : 0 ≤ N ^ 2 := by positivity
  have hbase : (N / 2 ^ n) * (N / 2 ^ n) = N ^ 2 * (1 / 4 : ℝ) ^ n := by
    rw [div_eq_mul_inv, div_eq_mul_inv, ← inv_pow]
    norm_num
    have hsq : ((1 / 2 : ℝ) ^ n) ^ 2 = (1 / 4 : ℝ) ^ n := by
      rw [← pow_mul, show n * 2 = 2 * n by ring, pow_mul]
      norm_num
    calc N * (1 / 2 : ℝ) ^ n * (N * (1 / 2 : ℝ) ^ n)
        = N ^ 2 * ((1 / 2 : ℝ) ^ n) ^ 2 := by ring
      _ = N ^ 2 * (1 / 4 : ℝ) ^ n := by rw [hsq]
  have hle : (N / 2 ^ n) * (N / 2 ^ n) ≤ (N ^ 2) * ((4 / 5 : ℝ) ^ n) ^ 3 := by
    rw [hbase, four_fifths_pow_cube]
    apply mul_le_mul_of_nonneg_left _ hN2
    apply pow_le_pow_left₀ (by norm_num) (by norm_num : (1 / 4 : ℝ) ≤ 64 / 125)
  have hmain := Real.rpow_le_rpow (by positivity) hle (by norm_num : (0 : ℝ) ≤ 1 / 3)
  rw [hbase, Real.mul_rpow hN2 (by positivity),
    Real.mul_rpow hN2 (by positivity)] at hmain
  have hcube : ((((4 / 5 : ℝ) ^ n) ^ 3) ^ (1 / 3 : ℝ)) = (4 / 5 : ℝ) ^ n := by
    rw [show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num,
      Real.pow_rpow_inv_natCast (by positivity : (0 : ℝ) ≤ (4 / 5 : ℝ) ^ n)
        (by norm_num : (3 : ℕ) ≠ 0)]
  rw [hcube] at hmain
  rw [hbase, Real.mul_rpow hN2 (by positivity)]
  exact hmain

theorem sqrt_div_pow_le {M : ℝ} (hM : 0 ≤ M) (n : ℕ) :
    Real.sqrt (M / 2 ^ n) ≤ Real.sqrt M * (4 / 5 : ℝ) ^ n := by
  have hbase : M / 2 ^ n = M * (1 / 2 : ℝ) ^ n := by
    rw [div_eq_mul_inv, ← inv_pow]
    norm_num
  calc Real.sqrt (M / 2 ^ n) = Real.sqrt (M * (1 / 2 : ℝ) ^ n) := by rw [hbase]
    _ = Real.sqrt M * Real.sqrt ((1 / 2 : ℝ) ^ n) := Real.sqrt_mul hM _
    _ ≤ Real.sqrt M * (4 / 5 : ℝ) ^ n := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg M)
        have h := Real.sqrt_le_sqrt (half_pow_le_sq n)
        rwa [Real.sqrt_sq (by positivity)] at h

theorem clawDetectCost_symm {N M l : ℝ} (hl : 0 < l) (hNM : l ^ 3 = N * M) :
    clawDetectCost N M l l = 3 * l * Real.log (2 * l) := by
  have hNMpos : 0 < N * M := by rw [← hNM]; positivity
  have hone : l * l / (N * M) = 1 / l := by
    rw [← hNM]
    field_simp
  have hden : (1 / l) * (l * l / (N * M)) = (1 / l) ^ 2 := by
    rw [hone]; ring
  simp only [clawDetectCost, szegedyCost, zero_add]
  rw [hden, Real.sqrt_sq (by positivity : (0:ℝ) ≤ 1 / l)]
  have hlne : l ≠ 0 := hl.ne'
  have harg : l + l = 2 * l := by ring
  rw [harg]
  field_simp
  ring

theorem clawDetectCost_symm_le {N M l N₀ : ℝ} (hl : 0 < l) (hNM : l ^ 3 = N * M)
    (hlle : l ≤ N₀) (hN₀ : 2 ≤ N₀) :
    clawDetectCost N M l l ≤ 6 * l * Real.log N₀ := by
  rw [clawDetectCost_symm hl hNM]
  have hN₀0 : 0 < N₀ := by linarith
  have hlogN₀ : 0 ≤ Real.log N₀ := Real.log_nonneg (by linarith)
  have h2l : (0 : ℝ) < 2 * l := by positivity
  have hle2 : 2 * l ≤ N₀ ^ 2 := by nlinarith
  have hlog : Real.log (2 * l) ≤ 2 * Real.log N₀ := by
    calc Real.log (2 * l) ≤ Real.log (N₀ ^ 2) := Real.log_le_log h2l hle2
      _ = 2 * Real.log N₀ := by rw [Real.log_pow]; push_cast; ring
  have h3 : 3 * l * Real.log (2 * l) ≤ 3 * l * (2 * Real.log N₀) := by
    apply mul_le_mul_of_nonneg_left hlog; positivity
  nlinarith

theorem rpow_third_le_sqrt {N M : ℝ} (hN : 0 ≤ N) (hM : 0 ≤ M) (hNM : N ^ 2 ≤ M) :
    (N * M) ^ (1 / 3 : ℝ) ≤ Real.sqrt M := by
  by_cases hN0 : N = 0
  · rw [hN0]; simp
  · have hNpos : 0 < N := lt_of_le_of_ne hN (Ne.symm hN0)
    have hMpos : 0 < M := by nlinarith
    have hNM0 : 0 < N * M := by positivity
    have hx : ((N * M) ^ (1 / 3 : ℝ)) ^ 3 = N * M := rpow_third_cube hNM0
    have hNle : N ≤ Real.sqrt M := by
      have h := Real.sqrt_le_sqrt hNM
      rwa [Real.sqrt_sq hN] at h
    have hcube : ((N * M) ^ (1 / 3 : ℝ)) ^ 3 ≤ (Real.sqrt M) ^ 3 := by
      rw [hx]
      calc N * M ≤ Real.sqrt M * M := mul_le_mul_of_nonneg_right hNle hM
        _ = (Real.sqrt M) ^ 3 := by
            rw [pow_succ, Real.sq_sqrt hM]
            ring
    exact le_of_pow_le_pow_left₀ (by norm_num : (3:ℕ) ≠ 0) (Real.sqrt_nonneg M) hcube

def clawSearchCost (N M : ℝ) (S2 S3 : ℕ) : ℝ :=
  (∑ s ∈ Finset.range S2, ((s : ℝ) + 1) *
      (if N ^ 2 ≤ M / 2 ^ (s + 1) then
        clawDetectCost N (M / 2 ^ (s + 1)) N N
      else
        clawDetectCost N (M / 2 ^ (s + 1))
          ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
          ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))))
  + (∑ s ∈ Finset.range S3, ((s : ℝ) + 1) *
      clawDetectCost (N / 2 ^ (s + 1)) (N / 2 ^ (s + 1))
        (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
        (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)))

def clawSearchStandardCost (N M : ℝ) (S2 S3 : ℕ) : ℝ :=
  (∑ s ∈ Finset.range S2, ((s : ℝ) + 1) *
      (if N ^ 2 ≤ M / 2 ^ (s + 1) then
        clawDetectStandardCost N (M / 2 ^ (s + 1)) N N
      else
        clawDetectStandardCost N (M / 2 ^ (s + 1))
          ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
          ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))))
  + (∑ s ∈ Finset.range S3, ((s : ℝ) + 1) *
      clawDetectStandardCost (N / 2 ^ (s + 1)) (N / 2 ^ (s + 1))
        (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
        (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)))

theorem div_pow_two_lt_self {M : ℝ} (hM : 0 < M) {n : ℕ} (hn : 0 < n) : M / 2 ^ n < M := by
  have hbase : M / 2 ^ n = M * (1 / 2 : ℝ) ^ n := by
    rw [div_eq_mul_inv, ← inv_pow]
    norm_num
  rw [hbase]
  have hpow : (1 / 2 : ℝ) ^ n < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have := mul_lt_mul_of_pos_left hpow hM
  simpa using this

theorem div_pow_two_le_self {M : ℝ} (hM : 0 ≤ M) (n : ℕ) : M / 2 ^ n ≤ M := by
  have hbase : M / 2 ^ n = M * (1 / 2 : ℝ) ^ n := by
    rw [div_eq_mul_inv, ← inv_pow]
    norm_num
  rw [hbase]
  have hpow : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_left hpow hM]

theorem theorem8_clawFinding_regime1 (N M : ℝ) (S2 S3 : ℕ) (hN : 2 ≤ N)
    (hNM : N ≤ M) (hM : M < N ^ 2) :
    clawSearchCost N M S2 S3 ≤ 4096 * (N * M) ^ (1 / 3 : ℝ) * Real.log N := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hM0 : (0 : ℝ) < M := by linarith
  have hNM0 : (0 : ℝ) < N * M := by positivity
  have hA : (0 : ℝ) ≤ (N * M) ^ (1 / 3 : ℝ) := le_of_lt (Real.rpow_pos_of_pos hNM0 _)
  have hlogN : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by linarith)

  have hstage2 :
      (∑ s ∈ Finset.range S2, ((s : ℝ) + 1) *
        (if N ^ 2 ≤ M / 2 ^ (s + 1) then
          clawDetectCost N (M / 2 ^ (s + 1)) N N
        else
          clawDetectCost N (M / 2 ^ (s + 1))
            ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
            ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))))
        ≤ 120 * (N * M) ^ (1 / 3 : ℝ) * Real.log N := by
    have hterm : ∀ s ∈ Finset.range S2,
        ((s : ℝ) + 1) *
          (if N ^ 2 ≤ M / 2 ^ (s + 1) then
            clawDetectCost N (M / 2 ^ (s + 1)) N N
          else
            clawDetectCost N (M / 2 ^ (s + 1))
              ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
              ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)))
        ≤ ((s : ℝ) + 1) *
            (6 * (N * M) ^ (1 / 3 : ℝ) * (4 / 5 : ℝ) ^ (s + 1) * Real.log N) := by
      intro s _
      have hMle : M / 2 ^ (s + 1) ≤ M := div_pow_two_le_self hM0.le (s + 1)
      have hnot : ¬ (N ^ 2 ≤ M / 2 ^ (s + 1)) := by
        intro hcon; linarith
      rw [if_neg hnot]
      have hM'pos : (0 : ℝ) < M / 2 ^ (s + 1) := by positivity
      have hNM' : (0 : ℝ) < N * (M / 2 ^ (s + 1)) := by positivity
      have hl3 : ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)) ^ 3
          = N * (M / 2 ^ (s + 1)) := rpow_third_cube hNM'
      have hlpos : (0 : ℝ) < (N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ) :=
        Real.rpow_pos_of_pos hNM' _
      have hlt : N * (M / 2 ^ (s + 1)) < N ^ 3 := by
        have h2 : N * (M / 2 ^ (s + 1)) ≤ N * M :=
          mul_le_mul_of_nonneg_left hMle hN0.le
        have h3 : N * M < N * N ^ 2 := mul_lt_mul_of_pos_left hM hN0
        nlinarith
      have hcube : ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)) ^ 3 < N ^ 3 := by
        rw [hl3]; exact hlt
      have hlle : (N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ) ≤ N :=
        le_of_lt (lt_of_pow_lt_pow_left₀ 3 hN0.le hcube)
      have hcost := clawDetectCost_symm_le hlpos hl3 hlle hN
      have hmaj := rpow_third_div_pow_le hN0.le hM0.le (s + 1)
      have hstep : (N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)
          ≤ (N * M) ^ (1 / 3 : ℝ) * (4 / 5 : ℝ) ^ (s + 1) := hmaj
      have h6 : (6 * (N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ) * Real.log N)
          ≤ 6 * ((N * M) ^ (1 / 3 : ℝ) * (4 / 5 : ℝ) ^ (s + 1)) * Real.log N := by
        apply mul_le_mul_of_nonneg_right _ hlogN
        nlinarith [hstep]
      have hcomb : clawDetectCost N (M / 2 ^ (s + 1))
            ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
            ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
          ≤ 6 * (N * M) ^ (1 / 3 : ℝ) * (4 / 5 : ℝ) ^ (s + 1) * Real.log N := by
        calc clawDetectCost N (M / 2 ^ (s + 1))
              ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
              ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
            ≤ 6 * (N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ) * Real.log N := hcost
          _ ≤ 6 * ((N * M) ^ (1 / 3 : ℝ) * (4 / 5 : ℝ) ^ (s + 1)) * Real.log N := h6
          _ = 6 * (N * M) ^ (1 / 3 : ℝ) * (4 / 5 : ℝ) ^ (s + 1) * Real.log N := by ring
      exact mul_le_mul_of_nonneg_left hcomb (by positivity)
    calc (∑ s ∈ Finset.range S2, ((s : ℝ) + 1) *
          (if N ^ 2 ≤ M / 2 ^ (s + 1) then
            clawDetectCost N (M / 2 ^ (s + 1)) N N
          else
            clawDetectCost N (M / 2 ^ (s + 1))
              ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
              ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))))
        ≤ ∑ s ∈ Finset.range S2, ((s : ℝ) + 1) *
            (6 * (N * M) ^ (1 / 3 : ℝ) * (4 / 5 : ℝ) ^ (s + 1) * Real.log N) :=
          Finset.sum_le_sum hterm
      _ = (6 * (N * M) ^ (1 / 3 : ℝ) * Real.log N) *
            ∑ s ∈ Finset.range S2, ((s : ℝ) + 1) * (4 / 5 : ℝ) ^ (s + 1) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          ring
      _ ≤ (6 * (N * M) ^ (1 / 3 : ℝ) * Real.log N) * 20 := by
          apply mul_le_mul_of_nonneg_left (weighted_geom_four_fifths_le S2)
          positivity
      _ = 120 * (N * M) ^ (1 / 3 : ℝ) * Real.log N := by ring

  have hstage3 :
      (∑ s ∈ Finset.range S3, ((s : ℝ) + 1) *
        clawDetectCost (N / 2 ^ (s + 1)) (N / 2 ^ (s + 1))
          (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
          (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)))
        ≤ 120 * (N * M) ^ (1 / 3 : ℝ) * Real.log N := by
    have hterm : ∀ s ∈ Finset.range S3,
        ((s : ℝ) + 1) *
          clawDetectCost (N / 2 ^ (s + 1)) (N / 2 ^ (s + 1))
            (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
            (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
        ≤ ((s : ℝ) + 1) *
            (6 * (N * M) ^ (1 / 3 : ℝ) * (4 / 5 : ℝ) ^ (s + 1) * Real.log N) := by
      intro s _
      have hNppos : (0 : ℝ) < N / 2 ^ (s + 1) := by positivity
      have hNM' : (0 : ℝ) < (N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1)) := by positivity
      have hl3 : (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)) ^ 3
          = (N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1)) := rpow_third_cube hNM'
      have hlpos : (0 : ℝ) < ((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ) :=
        Real.rpow_pos_of_pos hNM' _
      have hle_sq : (N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1)) ≤ N * N := by
        have hle : N / 2 ^ (s + 1) ≤ N := div_pow_two_le_self hN0.le (s + 1)
        exact mul_le_mul hle hle hNppos.le hN0.le
      have hlt3 : (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)) ^ 3 < N ^ 3 := by
        rw [hl3]
        nlinarith
      have hlle : ((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ) ≤ N :=
        le_of_lt (lt_of_pow_lt_pow_left₀ 3 hN0.le hlt3)
      have hcost := clawDetectCost_symm_le hlpos hl3 hlle hN
      have hmaj := rpow_third_sq_div_pow_le hN0.le (s + 1)
      have hA3 : (N ^ 2) ^ (1 / 3 : ℝ) ≤ (N * M) ^ (1 / 3 : ℝ) := by
        apply Real.rpow_le_rpow (by positivity) _ (by norm_num : (0 : ℝ) ≤ 1 / 3)
        nlinarith
      have hstep : ((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)
          ≤ (N * M) ^ (1 / 3 : ℝ) * (4 / 5 : ℝ) ^ (s + 1) := by
        calc ((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)
            ≤ (N ^ 2) ^ (1 / 3 : ℝ) * (4 / 5 : ℝ) ^ (s + 1) := hmaj
          _ ≤ (N * M) ^ (1 / 3 : ℝ) * (4 / 5 : ℝ) ^ (s + 1) := by
              apply mul_le_mul_of_nonneg_right hA3 (by positivity)
      have hcomb : clawDetectCost (N / 2 ^ (s + 1)) (N / 2 ^ (s + 1))
            (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
            (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
          ≤ 6 * (N * M) ^ (1 / 3 : ℝ) * (4 / 5 : ℝ) ^ (s + 1) * Real.log N := by
        calc clawDetectCost (N / 2 ^ (s + 1)) (N / 2 ^ (s + 1))
              (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
              (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
            ≤ 6 * ((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ) * Real.log N := hcost
          _ ≤ 6 * ((N * M) ^ (1 / 3 : ℝ) * (4 / 5 : ℝ) ^ (s + 1)) * Real.log N := by
              apply mul_le_mul_of_nonneg_right _ hlogN
              nlinarith [hstep]
          _ = 6 * (N * M) ^ (1 / 3 : ℝ) * (4 / 5 : ℝ) ^ (s + 1) * Real.log N := by ring
      exact mul_le_mul_of_nonneg_left hcomb (by positivity)
    calc (∑ s ∈ Finset.range S3, ((s : ℝ) + 1) *
          clawDetectCost (N / 2 ^ (s + 1)) (N / 2 ^ (s + 1))
            (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
            (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)))
        ≤ ∑ s ∈ Finset.range S3, ((s : ℝ) + 1) *
            (6 * (N * M) ^ (1 / 3 : ℝ) * (4 / 5 : ℝ) ^ (s + 1) * Real.log N) :=
          Finset.sum_le_sum hterm
      _ = (6 * (N * M) ^ (1 / 3 : ℝ) * Real.log N) *
            ∑ s ∈ Finset.range S3, ((s : ℝ) + 1) * (4 / 5 : ℝ) ^ (s + 1) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          ring
      _ ≤ (6 * (N * M) ^ (1 / 3 : ℝ) * Real.log N) * 20 := by
          apply mul_le_mul_of_nonneg_left (weighted_geom_four_fifths_le S3)
          positivity
      _ = 120 * (N * M) ^ (1 / 3 : ℝ) * Real.log N := by ring
  rw [clawSearchCost]
  have h240 : 240 * (N * M) ^ (1 / 3 : ℝ) * Real.log N
      ≤ 4096 * (N * M) ^ (1 / 3 : ℝ) * Real.log N := by
    have hx : (0 : ℝ) ≤ (N * M) ^ (1 / 3 : ℝ) * Real.log N := mul_nonneg hA hlogN
    nlinarith
  linarith

theorem clawDetectStandardCost_symm {N M l : ℝ} (hl : 0 < l) (hNM : l ^ 3 = N * M) :
    clawDetectStandardCost N M l l = 3 * l := by
  have hNMpos : 0 < N * M := by rw [← hNM]; positivity
  have hone : l * l / (N * M) = 1 / l := by
    rw [← hNM]; field_simp
  have hden : (1 / l) * (l * l / (N * M)) = (1 / l) ^ 2 := by rw [hone]; ring
  simp only [clawDetectStandardCost, szegedyCost]
  rw [hden, Real.sqrt_sq (by positivity : (0:ℝ) ≤ 1 / l)]
  have harg : l + l = 2 * l := by ring
  rw [harg]
  field_simp
  ring

theorem theorem8_clawFinding_regime2 (N M : ℝ) (S2 S3 : ℕ) (hN : 2 ≤ N)
    (hM : N ^ 2 ≤ M) :
    clawSearchCost N M S2 S3 ≤ 4096 * Real.sqrt M * Real.log N := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hM0 : (0 : ℝ) < M := by nlinarith
  have hNM0 : (0 : ℝ) < N * M := by positivity
  have hA : (0 : ℝ) ≤ (N * M) ^ (1 / 3 : ℝ) := le_of_lt (Real.rpow_pos_of_pos hNM0 _)
  have hlogN : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by linarith)
  have hsqrtM : (0 : ℝ) ≤ Real.sqrt M := Real.sqrt_nonneg M
  have hAsqrt : (N * M) ^ (1 / 3 : ℝ) ≤ Real.sqrt M :=
    rpow_third_le_sqrt hN0.le hM0.le hM

  have hstage2 :
      (∑ s ∈ Finset.range S2, ((s : ℝ) + 1) *
        (if N ^ 2 ≤ M / 2 ^ (s + 1) then
          clawDetectCost N (M / 2 ^ (s + 1)) N N
        else
          clawDetectCost N (M / 2 ^ (s + 1))
            ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
            ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))))
        ≤ 1280 * Real.sqrt M * Real.log N := by
    have hterm : ∀ s ∈ Finset.range S2,
        ((s : ℝ) + 1) *
          (if N ^ 2 ≤ M / 2 ^ (s + 1) then
            clawDetectCost N (M / 2 ^ (s + 1)) N N
          else
            clawDetectCost N (M / 2 ^ (s + 1))
              ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
              ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)))
        ≤ ((s : ℝ) + 1) *
            (64 * Real.sqrt M * (4 / 5 : ℝ) ^ (s + 1) * Real.log N) := by
      intro s _
      by_cases hcase : N ^ 2 ≤ M / 2 ^ (s + 1)
      · rw [if_pos hcase]
        have hcost := lemma4_clawDetect_regime2 N (M / 2 ^ (s + 1)) hN hcase
        have hsqrtle := sqrt_div_pow_le hM0.le (s + 1)
        have hcomb : clawDetectCost N (M / 2 ^ (s + 1)) N N
            ≤ 64 * Real.sqrt M * (4 / 5 : ℝ) ^ (s + 1) * Real.log N := by
          calc clawDetectCost N (M / 2 ^ (s + 1)) N N
              ≤ 64 * Real.sqrt (M / 2 ^ (s + 1)) * Real.log N := hcost
            _ ≤ 64 * (Real.sqrt M * (4 / 5 : ℝ) ^ (s + 1)) * Real.log N := by
                apply mul_le_mul_of_nonneg_right _ hlogN
                nlinarith [hsqrtle]
            _ = 64 * Real.sqrt M * (4 / 5 : ℝ) ^ (s + 1) * Real.log N := by ring
        exact mul_le_mul_of_nonneg_left hcomb (by positivity)
      · rw [if_neg hcase]
        have hM'pos : (0 : ℝ) < M / 2 ^ (s + 1) := by positivity
        have hNM' : (0 : ℝ) < N * (M / 2 ^ (s + 1)) := by positivity
        have hl3 : ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)) ^ 3
            = N * (M / 2 ^ (s + 1)) := rpow_third_cube hNM'
        have hlpos : (0 : ℝ) < (N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ) :=
          Real.rpow_pos_of_pos hNM' _
        have hlt : N * (M / 2 ^ (s + 1)) < N ^ 3 := by
          have h1 : M / 2 ^ (s + 1) < N ^ 2 := lt_of_not_ge hcase
          have h2 : N * (M / 2 ^ (s + 1)) < N * N ^ 2 :=
            mul_lt_mul_of_pos_left h1 hN0
          nlinarith
        have hcube : ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)) ^ 3 < N ^ 3 := by
          rw [hl3]; exact hlt
        have hlle : (N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ) ≤ N :=
          le_of_lt (lt_of_pow_lt_pow_left₀ 3 hN0.le hcube)
        have hcost := clawDetectCost_symm_le hlpos hl3 hlle hN
        have hmaj := rpow_third_div_pow_le hN0.le hM0.le (s + 1)
        have hcomb : clawDetectCost N (M / 2 ^ (s + 1))
              ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
              ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
            ≤ 64 * Real.sqrt M * (4 / 5 : ℝ) ^ (s + 1) * Real.log N := by
          have hstep : (N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)
              ≤ Real.sqrt M * (4 / 5 : ℝ) ^ (s + 1) := by
            calc (N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)
                ≤ (N * M) ^ (1 / 3 : ℝ) * (4 / 5 : ℝ) ^ (s + 1) := hmaj
              _ ≤ Real.sqrt M * (4 / 5 : ℝ) ^ (s + 1) := by
                  apply mul_le_mul_of_nonneg_right hAsqrt (by positivity)
          calc clawDetectCost N (M / 2 ^ (s + 1))
                ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
                ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
              ≤ 6 * (N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ) * Real.log N := hcost
            _ ≤ 6 * (Real.sqrt M * (4 / 5 : ℝ) ^ (s + 1)) * Real.log N := by
                apply mul_le_mul_of_nonneg_right _ hlogN
                nlinarith [hstep]
            _ ≤ 64 * Real.sqrt M * (4 / 5 : ℝ) ^ (s + 1) * Real.log N := by
                have hpos : (0 : ℝ) ≤ Real.sqrt M * (4 / 5 : ℝ) ^ (s + 1) * Real.log N := by
                  positivity
                nlinarith
        exact mul_le_mul_of_nonneg_left hcomb (by positivity)
    calc (∑ s ∈ Finset.range S2, ((s : ℝ) + 1) *
          (if N ^ 2 ≤ M / 2 ^ (s + 1) then
            clawDetectCost N (M / 2 ^ (s + 1)) N N
          else
            clawDetectCost N (M / 2 ^ (s + 1))
              ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
              ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))))
        ≤ ∑ s ∈ Finset.range S2, ((s : ℝ) + 1) *
            (64 * Real.sqrt M * (4 / 5 : ℝ) ^ (s + 1) * Real.log N) :=
          Finset.sum_le_sum hterm
      _ = (64 * Real.sqrt M * Real.log N) *
            ∑ s ∈ Finset.range S2, ((s : ℝ) + 1) * (4 / 5 : ℝ) ^ (s + 1) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          ring
      _ ≤ (64 * Real.sqrt M * Real.log N) * 20 := by
          apply mul_le_mul_of_nonneg_left (weighted_geom_four_fifths_le S2)
          positivity
      _ = 1280 * Real.sqrt M * Real.log N := by ring

  have hstage3 :
      (∑ s ∈ Finset.range S3, ((s : ℝ) + 1) *
        clawDetectCost (N / 2 ^ (s + 1)) (N / 2 ^ (s + 1))
          (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
          (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)))
        ≤ 120 * Real.sqrt M * Real.log N := by
    have hterm : ∀ s ∈ Finset.range S3,
        ((s : ℝ) + 1) *
          clawDetectCost (N / 2 ^ (s + 1)) (N / 2 ^ (s + 1))
            (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
            (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
        ≤ ((s : ℝ) + 1) * (6 * Real.sqrt M * (4 / 5 : ℝ) ^ (s + 1) * Real.log N) := by
      intro s _
      have hNppos : (0 : ℝ) < N / 2 ^ (s + 1) := by positivity
      have hNM' : (0 : ℝ) < (N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1)) := by positivity
      have hl3 : (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)) ^ 3
          = (N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1)) := rpow_third_cube hNM'
      have hlpos : (0 : ℝ) < ((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ) :=
        Real.rpow_pos_of_pos hNM' _
      have hle_sq : (N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1)) ≤ N * N := by
        have hle : N / 2 ^ (s + 1) ≤ N := div_pow_two_le_self hN0.le (s + 1)
        exact mul_le_mul hle hle hNppos.le hN0.le
      have hlt3 : (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)) ^ 3 < N ^ 3 := by
        rw [hl3]; nlinarith
      have hlle : ((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ) ≤ N :=
        le_of_lt (lt_of_pow_lt_pow_left₀ 3 hN0.le hlt3)
      have hcost := clawDetectCost_symm_le hlpos hl3 hlle hN
      have hmaj := rpow_third_sq_div_pow_le hN0.le (s + 1)
      have hstep : ((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)
          ≤ Real.sqrt M * (4 / 5 : ℝ) ^ (s + 1) := by
        calc ((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)
            ≤ (N ^ 2) ^ (1 / 3 : ℝ) * (4 / 5 : ℝ) ^ (s + 1) := hmaj
          _ ≤ Real.sqrt M * (4 / 5 : ℝ) ^ (s + 1) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              calc (N ^ 2) ^ (1 / 3 : ℝ) ≤ (N * M) ^ (1 / 3 : ℝ) := by
                    apply Real.rpow_le_rpow (by positivity) _ (by norm_num : (0:ℝ) ≤ 1/3)
                    nlinarith
                _ ≤ Real.sqrt M := hAsqrt
      have hcomb : clawDetectCost (N / 2 ^ (s + 1)) (N / 2 ^ (s + 1))
            (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
            (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
          ≤ 6 * Real.sqrt M * (4 / 5 : ℝ) ^ (s + 1) * Real.log N := by
        calc clawDetectCost (N / 2 ^ (s + 1)) (N / 2 ^ (s + 1))
              (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
              (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
            ≤ 6 * ((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ) * Real.log N := hcost
          _ ≤ 6 * (Real.sqrt M * (4 / 5 : ℝ) ^ (s + 1)) * Real.log N := by
              apply mul_le_mul_of_nonneg_right _ hlogN
              nlinarith [hstep]
          _ = 6 * Real.sqrt M * (4 / 5 : ℝ) ^ (s + 1) * Real.log N := by ring
      exact mul_le_mul_of_nonneg_left hcomb (by positivity)
    calc (∑ s ∈ Finset.range S3, ((s : ℝ) + 1) *
          clawDetectCost (N / 2 ^ (s + 1)) (N / 2 ^ (s + 1))
            (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
            (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)))
        ≤ ∑ s ∈ Finset.range S3, ((s : ℝ) + 1) *
            (6 * Real.sqrt M * (4 / 5 : ℝ) ^ (s + 1) * Real.log N) :=
          Finset.sum_le_sum hterm
      _ = (6 * Real.sqrt M * Real.log N) *
            ∑ s ∈ Finset.range S3, ((s : ℝ) + 1) * (4 / 5 : ℝ) ^ (s + 1) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          ring
      _ ≤ (6 * Real.sqrt M * Real.log N) * 20 := by
          apply mul_le_mul_of_nonneg_left (weighted_geom_four_fifths_le S3)
          positivity
      _ = 120 * Real.sqrt M * Real.log N := by ring
  rw [clawSearchCost]
  have hx : (0 : ℝ) ≤ Real.sqrt M * Real.log N := mul_nonneg hsqrtM hlogN
  have hfin : 1280 * Real.sqrt M * Real.log N + 120 * Real.sqrt M * Real.log N
      ≤ 4096 * Real.sqrt M * Real.log N := by nlinarith
  linarith

theorem corollary9_clawFinding_regime1 (N M : ℝ) (S2 S3 : ℕ) (hN : 2 ≤ N)
    (hNM : N ≤ M) (hM : M < N ^ 2) :
    clawSearchStandardCost N M S2 S3 ≤ 1024 * (N * M) ^ (1 / 3 : ℝ) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hM0 : (0 : ℝ) < M := by linarith
  have hNM0 : (0 : ℝ) < N * M := by positivity
  have hA : (0 : ℝ) ≤ (N * M) ^ (1 / 3 : ℝ) := le_of_lt (Real.rpow_pos_of_pos hNM0 _)
  have hstage2 :
      (∑ s ∈ Finset.range S2, ((s : ℝ) + 1) *
        (if N ^ 2 ≤ M / 2 ^ (s + 1) then
          clawDetectStandardCost N (M / 2 ^ (s + 1)) N N
        else
          clawDetectStandardCost N (M / 2 ^ (s + 1))
            ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
            ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))))
        ≤ 60 * (N * M) ^ (1 / 3 : ℝ) := by
    have hterm : ∀ s ∈ Finset.range S2,
        ((s : ℝ) + 1) *
          (if N ^ 2 ≤ M / 2 ^ (s + 1) then
            clawDetectStandardCost N (M / 2 ^ (s + 1)) N N
          else
            clawDetectStandardCost N (M / 2 ^ (s + 1))
              ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
              ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)))
        ≤ ((s : ℝ) + 1) * (3 * (N * M) ^ (1 / 3 : ℝ) * (4 / 5 : ℝ) ^ (s + 1)) := by
      intro s _
      have hMle : M / 2 ^ (s + 1) ≤ M := div_pow_two_le_self hM0.le (s + 1)
      have hnot : ¬ (N ^ 2 ≤ M / 2 ^ (s + 1)) := by intro hcon; linarith
      rw [if_neg hnot]
      have hM'pos : (0 : ℝ) < M / 2 ^ (s + 1) := by positivity
      have hNM' : (0 : ℝ) < N * (M / 2 ^ (s + 1)) := by positivity
      have hl3 : ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)) ^ 3
          = N * (M / 2 ^ (s + 1)) := rpow_third_cube hNM'
      have hlpos : (0 : ℝ) < (N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ) :=
        Real.rpow_pos_of_pos hNM' _
      have hcost := clawDetectStandardCost_symm hlpos hl3
      have hmaj := rpow_third_div_pow_le hN0.le hM0.le (s + 1)
      have hcomb : clawDetectStandardCost N (M / 2 ^ (s + 1))
            ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
            ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
          ≤ 3 * (N * M) ^ (1 / 3 : ℝ) * (4 / 5 : ℝ) ^ (s + 1) := by
        calc clawDetectStandardCost N (M / 2 ^ (s + 1))
              ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
              ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
            = 3 * (N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ) := hcost
          _ ≤ 3 * ((N * M) ^ (1 / 3 : ℝ) * (4 / 5 : ℝ) ^ (s + 1)) := by
              nlinarith [hmaj]
          _ = 3 * (N * M) ^ (1 / 3 : ℝ) * (4 / 5 : ℝ) ^ (s + 1) := by ring
      exact mul_le_mul_of_nonneg_left hcomb (by positivity)
    calc (∑ s ∈ Finset.range S2, ((s : ℝ) + 1) *
          (if N ^ 2 ≤ M / 2 ^ (s + 1) then
            clawDetectStandardCost N (M / 2 ^ (s + 1)) N N
          else
            clawDetectStandardCost N (M / 2 ^ (s + 1))
              ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
              ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))))
        ≤ ∑ s ∈ Finset.range S2, ((s : ℝ) + 1) *
            (3 * (N * M) ^ (1 / 3 : ℝ) * (4 / 5 : ℝ) ^ (s + 1)) :=
          Finset.sum_le_sum hterm
      _ = (3 * (N * M) ^ (1 / 3 : ℝ)) *
            ∑ s ∈ Finset.range S2, ((s : ℝ) + 1) * (4 / 5 : ℝ) ^ (s + 1) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          ring
      _ ≤ (3 * (N * M) ^ (1 / 3 : ℝ)) * 20 := by
          apply mul_le_mul_of_nonneg_left (weighted_geom_four_fifths_le S2)
          positivity
      _ = 60 * (N * M) ^ (1 / 3 : ℝ) := by ring
  have hstage3 :
      (∑ s ∈ Finset.range S3, ((s : ℝ) + 1) *
        clawDetectStandardCost (N / 2 ^ (s + 1)) (N / 2 ^ (s + 1))
          (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
          (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)))
        ≤ 60 * (N * M) ^ (1 / 3 : ℝ) := by
    have hterm : ∀ s ∈ Finset.range S3,
        ((s : ℝ) + 1) *
          clawDetectStandardCost (N / 2 ^ (s + 1)) (N / 2 ^ (s + 1))
            (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
            (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
        ≤ ((s : ℝ) + 1) * (3 * (N * M) ^ (1 / 3 : ℝ) * (4 / 5 : ℝ) ^ (s + 1)) := by
      intro s _
      have hNppos : (0 : ℝ) < N / 2 ^ (s + 1) := by positivity
      have hNM' : (0 : ℝ) < (N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1)) := by positivity
      have hl3 : (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)) ^ 3
          = (N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1)) := rpow_third_cube hNM'
      have hlpos : (0 : ℝ) < ((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ) :=
        Real.rpow_pos_of_pos hNM' _
      have hcost := clawDetectStandardCost_symm hlpos hl3
      have hmaj := rpow_third_sq_div_pow_le hN0.le (s + 1)
      have hA3 : (N ^ 2) ^ (1 / 3 : ℝ) ≤ (N * M) ^ (1 / 3 : ℝ) := by
        apply Real.rpow_le_rpow (by positivity) _ (by norm_num : (0 : ℝ) ≤ 1 / 3)
        nlinarith
      have hstep : ((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)
          ≤ (N * M) ^ (1 / 3 : ℝ) * (4 / 5 : ℝ) ^ (s + 1) := by
        calc ((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)
            ≤ (N ^ 2) ^ (1 / 3 : ℝ) * (4 / 5 : ℝ) ^ (s + 1) := hmaj
          _ ≤ (N * M) ^ (1 / 3 : ℝ) * (4 / 5 : ℝ) ^ (s + 1) := by
              apply mul_le_mul_of_nonneg_right hA3 (by positivity)
      have hcomb : clawDetectStandardCost (N / 2 ^ (s + 1)) (N / 2 ^ (s + 1))
            (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
            (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
          ≤ 3 * (N * M) ^ (1 / 3 : ℝ) * (4 / 5 : ℝ) ^ (s + 1) := by
        calc clawDetectStandardCost (N / 2 ^ (s + 1)) (N / 2 ^ (s + 1))
              (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
              (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
            = 3 * ((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ) := hcost
          _ ≤ 3 * ((N * M) ^ (1 / 3 : ℝ) * (4 / 5 : ℝ) ^ (s + 1)) := by
              nlinarith [hstep]
          _ = 3 * (N * M) ^ (1 / 3 : ℝ) * (4 / 5 : ℝ) ^ (s + 1) := by ring
      exact mul_le_mul_of_nonneg_left hcomb (by positivity)
    calc (∑ s ∈ Finset.range S3, ((s : ℝ) + 1) *
          clawDetectStandardCost (N / 2 ^ (s + 1)) (N / 2 ^ (s + 1))
            (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
            (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)))
        ≤ ∑ s ∈ Finset.range S3, ((s : ℝ) + 1) *
            (3 * (N * M) ^ (1 / 3 : ℝ) * (4 / 5 : ℝ) ^ (s + 1)) :=
          Finset.sum_le_sum hterm
      _ = (3 * (N * M) ^ (1 / 3 : ℝ)) *
            ∑ s ∈ Finset.range S3, ((s : ℝ) + 1) * (4 / 5 : ℝ) ^ (s + 1) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          ring
      _ ≤ (3 * (N * M) ^ (1 / 3 : ℝ)) * 20 := by
          apply mul_le_mul_of_nonneg_left (weighted_geom_four_fifths_le S3)
          positivity
      _ = 60 * (N * M) ^ (1 / 3 : ℝ) := by ring
  rw [clawSearchStandardCost]
  have hfin : 60 * (N * M) ^ (1 / 3 : ℝ) + 60 * (N * M) ^ (1 / 3 : ℝ)
      ≤ 1024 * (N * M) ^ (1 / 3 : ℝ) := by nlinarith
  linarith

theorem corollary9_clawFinding_regime2 (N M : ℝ) (S2 S3 : ℕ) (hN : 2 ≤ N)
    (hM : N ^ 2 ≤ M) :
    clawSearchStandardCost N M S2 S3 ≤ 1024 * Real.sqrt M := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hM0 : (0 : ℝ) < M := by nlinarith
  have hNM0 : (0 : ℝ) < N * M := by positivity
  have hsqrtM : (0 : ℝ) ≤ Real.sqrt M := Real.sqrt_nonneg M
  have hAsqrt : (N * M) ^ (1 / 3 : ℝ) ≤ Real.sqrt M :=
    rpow_third_le_sqrt hN0.le hM0.le hM
  have hstage2 :
      (∑ s ∈ Finset.range S2, ((s : ℝ) + 1) *
        (if N ^ 2 ≤ M / 2 ^ (s + 1) then
          clawDetectStandardCost N (M / 2 ^ (s + 1)) N N
        else
          clawDetectStandardCost N (M / 2 ^ (s + 1))
            ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
            ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))))
        ≤ 80 * Real.sqrt M := by
    have hterm : ∀ s ∈ Finset.range S2,
        ((s : ℝ) + 1) *
          (if N ^ 2 ≤ M / 2 ^ (s + 1) then
            clawDetectStandardCost N (M / 2 ^ (s + 1)) N N
          else
            clawDetectStandardCost N (M / 2 ^ (s + 1))
              ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
              ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)))
        ≤ ((s : ℝ) + 1) * (4 * Real.sqrt M * (4 / 5 : ℝ) ^ (s + 1)) := by
      intro s _
      by_cases hcase : N ^ 2 ≤ M / 2 ^ (s + 1)
      · rw [if_pos hcase]
        have hcost := corollary5_clawDetect_standard_regime2 N (M / 2 ^ (s + 1)) hN hcase
        have hsqrtle := sqrt_div_pow_le hM0.le (s + 1)
        have hcomb : clawDetectStandardCost N (M / 2 ^ (s + 1)) N N
            ≤ 4 * Real.sqrt M * (4 / 5 : ℝ) ^ (s + 1) := by
          calc clawDetectStandardCost N (M / 2 ^ (s + 1)) N N
              ≤ 4 * Real.sqrt (M / 2 ^ (s + 1)) := hcost
            _ ≤ 4 * (Real.sqrt M * (4 / 5 : ℝ) ^ (s + 1)) := by nlinarith [hsqrtle]
            _ = 4 * Real.sqrt M * (4 / 5 : ℝ) ^ (s + 1) := by ring
        exact mul_le_mul_of_nonneg_left hcomb (by positivity)
      · rw [if_neg hcase]
        have hM'pos : (0 : ℝ) < M / 2 ^ (s + 1) := by positivity
        have hNM' : (0 : ℝ) < N * (M / 2 ^ (s + 1)) := by positivity
        have hl3 : ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)) ^ 3
            = N * (M / 2 ^ (s + 1)) := rpow_third_cube hNM'
        have hlpos : (0 : ℝ) < (N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ) :=
          Real.rpow_pos_of_pos hNM' _
        have hcost := clawDetectStandardCost_symm hlpos hl3
        have hmaj := rpow_third_div_pow_le hN0.le hM0.le (s + 1)
        have hcomb : clawDetectStandardCost N (M / 2 ^ (s + 1))
              ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
              ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
            ≤ 4 * Real.sqrt M * (4 / 5 : ℝ) ^ (s + 1) := by
          have hstep : (N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)
              ≤ Real.sqrt M * (4 / 5 : ℝ) ^ (s + 1) := by
            calc (N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)
                ≤ (N * M) ^ (1 / 3 : ℝ) * (4 / 5 : ℝ) ^ (s + 1) := hmaj
              _ ≤ Real.sqrt M * (4 / 5 : ℝ) ^ (s + 1) := by
                  apply mul_le_mul_of_nonneg_right hAsqrt (by positivity)
          calc clawDetectStandardCost N (M / 2 ^ (s + 1))
                ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
                ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
              = 3 * (N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ) := hcost
            _ ≤ 3 * (Real.sqrt M * (4 / 5 : ℝ) ^ (s + 1)) := by nlinarith [hstep]
            _ ≤ 4 * Real.sqrt M * (4 / 5 : ℝ) ^ (s + 1) := by
                have hpos : (0 : ℝ) ≤ Real.sqrt M * (4 / 5 : ℝ) ^ (s + 1) := by positivity
                nlinarith
        exact mul_le_mul_of_nonneg_left hcomb (by positivity)
    calc (∑ s ∈ Finset.range S2, ((s : ℝ) + 1) *
          (if N ^ 2 ≤ M / 2 ^ (s + 1) then
            clawDetectStandardCost N (M / 2 ^ (s + 1)) N N
          else
            clawDetectStandardCost N (M / 2 ^ (s + 1))
              ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
              ((N * (M / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))))
        ≤ ∑ s ∈ Finset.range S2, ((s : ℝ) + 1) *
            (4 * Real.sqrt M * (4 / 5 : ℝ) ^ (s + 1)) :=
          Finset.sum_le_sum hterm
      _ = (4 * Real.sqrt M) *
            ∑ s ∈ Finset.range S2, ((s : ℝ) + 1) * (4 / 5 : ℝ) ^ (s + 1) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          ring
      _ ≤ (4 * Real.sqrt M) * 20 := by
          apply mul_le_mul_of_nonneg_left (weighted_geom_four_fifths_le S2)
          positivity
      _ = 80 * Real.sqrt M := by ring
  have hstage3 :
      (∑ s ∈ Finset.range S3, ((s : ℝ) + 1) *
        clawDetectStandardCost (N / 2 ^ (s + 1)) (N / 2 ^ (s + 1))
          (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
          (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)))
        ≤ 60 * Real.sqrt M := by
    have hterm : ∀ s ∈ Finset.range S3,
        ((s : ℝ) + 1) *
          clawDetectStandardCost (N / 2 ^ (s + 1)) (N / 2 ^ (s + 1))
            (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
            (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
        ≤ ((s : ℝ) + 1) * (3 * Real.sqrt M * (4 / 5 : ℝ) ^ (s + 1)) := by
      intro s _
      have hNppos : (0 : ℝ) < N / 2 ^ (s + 1) := by positivity
      have hNM' : (0 : ℝ) < (N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1)) := by positivity
      have hl3 : (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)) ^ 3
          = (N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1)) := rpow_third_cube hNM'
      have hlpos : (0 : ℝ) < ((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ) :=
        Real.rpow_pos_of_pos hNM' _
      have hcost := clawDetectStandardCost_symm hlpos hl3
      have hmaj := rpow_third_sq_div_pow_le hN0.le (s + 1)
      have hstep : ((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)
          ≤ Real.sqrt M * (4 / 5 : ℝ) ^ (s + 1) := by
        calc ((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)
            ≤ (N ^ 2) ^ (1 / 3 : ℝ) * (4 / 5 : ℝ) ^ (s + 1) := hmaj
          _ ≤ Real.sqrt M * (4 / 5 : ℝ) ^ (s + 1) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              calc (N ^ 2) ^ (1 / 3 : ℝ) ≤ (N * M) ^ (1 / 3 : ℝ) := by
                    apply Real.rpow_le_rpow (by positivity) _ (by norm_num : (0:ℝ) ≤ 1/3)
                    nlinarith
                _ ≤ Real.sqrt M := hAsqrt
      have hcomb : clawDetectStandardCost (N / 2 ^ (s + 1)) (N / 2 ^ (s + 1))
            (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
            (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
          ≤ 3 * Real.sqrt M * (4 / 5 : ℝ) ^ (s + 1) := by
        calc clawDetectStandardCost (N / 2 ^ (s + 1)) (N / 2 ^ (s + 1))
              (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
              (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
            = 3 * ((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ) := hcost
          _ ≤ 3 * (Real.sqrt M * (4 / 5 : ℝ) ^ (s + 1)) := by nlinarith [hstep]
          _ = 3 * Real.sqrt M * (4 / 5 : ℝ) ^ (s + 1) := by ring
      exact mul_le_mul_of_nonneg_left hcomb (by positivity)
    calc (∑ s ∈ Finset.range S3, ((s : ℝ) + 1) *
          clawDetectStandardCost (N / 2 ^ (s + 1)) (N / 2 ^ (s + 1))
            (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ))
            (((N / 2 ^ (s + 1)) * (N / 2 ^ (s + 1))) ^ (1 / 3 : ℝ)))
        ≤ ∑ s ∈ Finset.range S3, ((s : ℝ) + 1) *
            (3 * Real.sqrt M * (4 / 5 : ℝ) ^ (s + 1)) :=
          Finset.sum_le_sum hterm
      _ = (3 * Real.sqrt M) *
            ∑ s ∈ Finset.range S3, ((s : ℝ) + 1) * (4 / 5 : ℝ) ^ (s + 1) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          ring
      _ ≤ (3 * Real.sqrt M) * 20 := by
          apply mul_le_mul_of_nonneg_left (weighted_geom_four_fifths_le S3)
          positivity
      _ = 60 * Real.sqrt M := by ring
  rw [clawSearchStandardCost]
  have hfin : 80 * Real.sqrt M + 60 * Real.sqrt M ≤ 1024 * Real.sqrt M := by nlinarith
  linarith

theorem weighted_geom_le_of_le {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 4 / 5) (S : ℕ) :
    (∑ s ∈ Finset.range S, ((s : ℝ) + 1) * r ^ (s + 1)) ≤ 20 := by
  have hmono : (∑ s ∈ Finset.range S, ((s : ℝ) + 1) * r ^ (s + 1))
      ≤ ∑ s ∈ Finset.range S, ((s : ℝ) + 1) * (4 / 5 : ℝ) ^ (s + 1) := by
    apply Finset.sum_le_sum
    intro s _
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀ hr0 hr (s + 1)
  exact le_trans hmono (weighted_geom_four_fifths_le S)

theorem rpow_ratio_le {k : ℕ} (hk : 2 ≤ k) :
    (2 : ℝ) ^ (-(((k : ℝ) - 1) / ((k : ℝ) + 1))) ≤ 4 / 5 := by
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hexp : (1 / 3 : ℝ) ≤ ((k : ℝ) - 1) / ((k : ℝ) + 1) := by
    field_simp
    nlinarith
  have hmono : (2 : ℝ) ^ (1 / 3 : ℝ) ≤ (2 : ℝ) ^ (((k : ℝ) - 1) / ((k : ℝ) + 1)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hpos1 : (0 : ℝ) < (2 : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hinv : ((2 : ℝ) ^ (((k : ℝ) - 1) / ((k : ℝ) + 1)))⁻¹ ≤ ((2 : ℝ) ^ (1 / 3 : ℝ))⁻¹ := by
    have h := one_div_le_one_div_of_le hpos1 hmono
    simpa [one_div] using h
  have hneg : (2 : ℝ) ^ (-(((k : ℝ) - 1) / ((k : ℝ) + 1)))
      = ((2 : ℝ) ^ (((k : ℝ) - 1) / ((k : ℝ) + 1)))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  rw [hneg]
  have hc3 : ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = 2 := by
    have h := rpow_third_cube (N := 2) (M := 1) (by norm_num)
    simpa using h
  have hcinv3 : (((2 : ℝ) ^ (1 / 3 : ℝ))⁻¹) ^ 3 = (1 / 2 : ℝ) := by
    rw [inv_pow, hc3]
    norm_num
  have hhalf : (1 / 2 : ℝ) ≤ (4 / 5 : ℝ) ^ 3 := by norm_num
  have hle : ((2 : ℝ) ^ (1 / 3 : ℝ))⁻¹ ≤ 4 / 5 :=
    le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 4 / 5)
      (by rw [hcinv3]; exact hhalf)
  exact le_trans hinv hle

theorem klevel_factor {P : ℝ} (hP : 0 ≤ P) {k : ℕ} (hk : 1 ≤ k) (s : ℕ) :
    (P / 2 ^ ((s + 1) * (k - 1))) ^ (1 / ((k : ℝ) + 1))
      = P ^ (1 / ((k : ℝ) + 1))
          * ((2 : ℝ) ^ (-(((k : ℝ) - 1) / ((k : ℝ) + 1)))) ^ (s + 1) := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hKpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hKne : ((k : ℝ) + 1) ≠ 0 := hKpos.ne'
  have hden : ((2 : ℝ) ^ ((s + 1) * (k - 1))) ^ (1 / ((k : ℝ) + 1))
      = (2 : ℝ) ^ ((((s + 1) * (k - 1) : ℕ) : ℝ) * (1 / ((k : ℝ) + 1))) := by
    rw [← Real.rpow_natCast (x := (2:ℝ))]
    exact (Real.rpow_mul h2 _ _).symm
  rw [Real.div_rpow hP (by positivity), hden]
  have hneg : ((2 : ℝ) ^ ((((s + 1) * (k - 1) : ℕ) : ℝ) * (1 / ((k : ℝ) + 1))))⁻¹
      = (2 : ℝ) ^ (-(((((s + 1) * (k - 1) : ℕ) : ℝ) * (1 / ((k : ℝ) + 1))))) :=
    (Real.rpow_neg h2 _).symm
  rw [div_eq_mul_inv, hneg]
  have hk1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub hk]
    norm_num
  have hexp : -(((((s + 1) * (k - 1) : ℕ) : ℝ) * (1 / ((k : ℝ) + 1))))
      = (-(((k : ℝ) - 1) / ((k : ℝ) + 1))) * ((s : ℝ) + 1) := by
    push_cast
    rw [hk1]
    field_simp
  rw [hexp]
  rw [show ((s : ℝ) + 1) = ((s + 1 : ℕ) : ℝ) by push_cast; ring]
  rw [Real.rpow_mul_natCast h2]

theorem rpow_div_pow_factor {X : ℝ} (hX : 0 ≤ X) (e : ℝ) (q m : ℕ) :
    (X / 2 ^ (m * q)) ^ e = X ^ e * ((2 : ℝ) ^ (-((q : ℝ) * e))) ^ m := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hden : ((2 : ℝ) ^ (m * q)) ^ e
      = (2 : ℝ) ^ (((m * q : ℕ) : ℝ) * e) := by
    rw [← Real.rpow_natCast (x := (2:ℝ))]
    exact (Real.rpow_mul h2 _ _).symm
  rw [Real.div_rpow hX (by positivity), hden]
  have hneg : ((2 : ℝ) ^ (((m * q : ℕ) : ℝ) * e))⁻¹
      = (2 : ℝ) ^ (-(((m * q : ℕ) : ℝ) * e)) := (Real.rpow_neg h2 _).symm
  rw [div_eq_mul_inv, hneg]
  have hexp : -((((m * q : ℕ) : ℝ) * e)) = (-((q : ℝ) * e)) * (m : ℝ) := by
    push_cast
    ring
  rw [hexp, Real.rpow_mul_natCast h2]

theorem two_rpow_neg_le_four_fifths {k q : ℕ} (hk : 2 ≤ k) (hq : k - 1 ≤ q) :
    (2 : ℝ) ^ (-((q : ℝ) / ((k : ℝ) + 1))) ≤ 4 / 5 := by
  have hkR : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hcast : ((k - 1 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hk1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    norm_num
  have hexp : ((k : ℝ) - 1) / ((k : ℝ) + 1) ≤ (q : ℝ) / ((k : ℝ) + 1) := by
    rw [← hk1]
    exact div_le_div_of_nonneg_right hcast hkR.le
  have hmono : (2 : ℝ) ^ (-((q : ℝ) / ((k : ℝ) + 1)))
      ≤ (2 : ℝ) ^ (-(((k : ℝ) - 1) / ((k : ℝ) + 1))) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    exact neg_le_neg hexp
  exact le_trans hmono (rpow_ratio_le hk)

theorem klevel_regime1_major {k : ℕ} (hk : 2 ≤ k) {P : ℝ} (hP : 0 ≤ P) {q : ℕ}
    (hq : k - 1 ≤ q) (m : ℕ) :
    (P / 2 ^ (m * q)) ^ (1 / ((k : ℝ) + 1))
      ≤ P ^ (1 / ((k : ℝ) + 1)) * (4 / 5 : ℝ) ^ m := by
  rw [rpow_div_pow_factor hP]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hr : (2 : ℝ) ^ (-((q : ℝ) * (1 / ((k : ℝ) + 1)))) ≤ 4 / 5 := by
    have h := two_rpow_neg_le_four_fifths hk hq
    convert h using 2
    ring
  exact pow_le_pow_left₀ (by positivity) hr m

theorem two_rpow_neg_half_le {q : ℕ} (hq : 1 ≤ q) :
    (2 : ℝ) ^ (-((q : ℝ) * (1/2))) ≤ 4 / 5 := by
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hexp : (1/3 : ℝ) ≤ (q : ℝ) * (1/2) := by linarith
  have hmono : (2 : ℝ) ^ (-((q : ℝ) * (1/2))) ≤ (2 : ℝ) ^ (-(1/3 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    linarith
  have hmatch : (2 : ℝ) ^ (-(1/3 : ℝ)) = (2 : ℝ) ^ (-(((2 : ℝ) - 1) / ((2 : ℝ) + 1))) := by
    norm_num
  rw [hmatch] at hmono
  exact le_trans hmono (rpow_ratio_le (by norm_num : 2 ≤ 2))

theorem sqrt_div_pow_factor {X : ℝ} (hX : 0 ≤ X) (q m : ℕ) :
    Real.sqrt (X / 2 ^ (m * q))
      = Real.sqrt X * ((2 : ℝ) ^ (-((q : ℝ) * (1/2)))) ^ m := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact rpow_div_pow_factor hX (1/2) q m

theorem klevel_base_le_regime2 {k : ℕ} (hk : 2 ≤ k) {N1 A : ℝ} (hN1 : 0 < N1) (hA : 0 < A)
    (hAk : N1 ^ k ≤ A) :
    (N1 * A) ^ (1 / ((k : ℝ) + 1)) ≤ Real.sqrt (A / N1 ^ (k - 2)) := by
  have hN1le : (0 : ℝ) ≤ N1 := hN1.le
  have hAle : (0 : ℝ) ≤ A := hA.le
  have hPA : (0 : ℝ) ≤ N1 * A := by positivity
  have hX : (0 : ℝ) ≤ A / N1 ^ (k - 2) := by positivity
  rw [Real.sqrt_eq_rpow]
  have hn : 2 * (k + 1) ≠ 0 := by omega
  have hb0 : (0 : ℝ) ≤ (A / N1 ^ (k - 2)) ^ (1/2 : ℝ) := Real.rpow_nonneg hX _
  apply le_of_pow_le_pow_left₀ hn hb0
  have he : (1 / ((k : ℝ) + 1)) * (((2 * (k + 1) : ℕ)) : ℝ) = 2 := by
    push_cast
    field_simp
  have he2 : (1/2 : ℝ) * (((2 * (k + 1) : ℕ)) : ℝ) = (((k + 1 : ℕ)) : ℝ) := by
    push_cast
    ring
  have hpow : N1 ^ (k * (k - 1)) ≤ A ^ (k - 1) := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ N1 ^ k) hAk (k - 1)
    rwa [← pow_mul] at h
  have hexp2 : 2 + (k - 2) * (k + 1) = k * (k - 1) := by
    have hk1 : 1 ≤ k := by omega
    have h1 : ((k - 2 : ℕ) : ℤ) = (k : ℤ) - 2 := by
      rw [Nat.cast_sub hk]; norm_num
    have h2 : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by
      rw [Nat.cast_sub hk1]; norm_num
    have hmain : ((2 + (k - 2) * (k + 1) : ℕ) : ℤ) = ((k * (k - 1) : ℕ) : ℤ) := by
      push_cast
      rw [h1, h2]
      ring
    exact_mod_cast hmain
  have hkey : N1 ^ (k * (k - 1)) * A ^ 2 ≤ A ^ (k + 1) := by
    have hAeq : A ^ (k + 1) = A ^ (k - 1) * A ^ 2 := by
      rw [show k + 1 = (k - 1) + 2 by omega, pow_add]
    rw [hAeq]
    exact mul_le_mul_of_nonneg_right hpow (sq_nonneg A)
  have hcore : (N1 * A) ^ 2 ≤ (A / N1 ^ (k - 2)) ^ (k + 1) := by
    have hden : (A / N1 ^ (k - 2)) ^ (k + 1) = A ^ (k + 1) / N1 ^ ((k - 2) * (k + 1)) := by
      rw [div_pow, pow_mul]
    rw [hden, le_div_iff₀ (by positivity : (0 : ℝ) < N1 ^ ((k - 2) * (k + 1)))]
    have hsplit : (N1 * A) ^ 2 * N1 ^ ((k - 2) * (k + 1))
        = N1 ^ (2 + (k - 2) * (k + 1)) * A ^ 2 := by
      rw [show (N1 * A) ^ 2 = N1 ^ 2 * A ^ 2 by ring, mul_assoc,
        mul_comm (A ^ 2) (N1 ^ ((k - 2) * (k + 1))), ← mul_assoc, ← pow_add]
    rw [hsplit, hexp2]
    exact hkey
  calc ((N1 * A) ^ (1 / ((k : ℝ) + 1))) ^ (2 * (k + 1))
      = (N1 * A) ^ ((1 / ((k : ℝ) + 1)) * (((2 * (k + 1) : ℕ)) : ℝ)) := by
        rw [Real.rpow_mul_natCast hPA]
    _ = (N1 * A) ^ (2 : ℝ) := by rw [he]
    _ = (N1 * A) ^ 2 := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    _ ≤ (A / N1 ^ (k - 2)) ^ (k + 1) := hcore
    _ = ((A / N1 ^ (k - 2)) ^ (1/2 : ℝ)) ^ (2 * (k + 1)) := by
        rw [← Real.rpow_mul_natCast hX (1/2) (2 * (k + 1)), he2, Real.rpow_natCast]

def kSeqCost (k : ℕ) (N1 A : ℝ) (q : ℕ) (S : ℕ) : ℝ :=
  ∑ s ∈ Finset.range S, ((s : ℝ) + 1) *
    (if N1 ^ k ≤ A / 2 ^ ((s + 1) * q) then
      kClawDetectCost k (N1 * (A / 2 ^ ((s + 1) * q))) N1
    else
      kClawDetectCost k (N1 * (A / 2 ^ ((s + 1) * q)))
        ((N1 * (A / 2 ^ ((s + 1) * q))) ^ (1 / ((k : ℝ) + 1))))

def kSeqStandardCost (k : ℕ) (N1 A : ℝ) (q : ℕ) (S : ℕ) : ℝ :=
  ∑ s ∈ Finset.range S, ((s : ℝ) + 1) *
    (if N1 ^ k ≤ A / 2 ^ ((s + 1) * q) then
      kClawDetectStandardCost k (N1 * (A / 2 ^ ((s + 1) * q))) N1
    else
      kClawDetectStandardCost k (N1 * (A / 2 ^ ((s + 1) * q)))
        ((N1 * (A / 2 ^ ((s + 1) * q))) ^ (1 / ((k : ℝ) + 1))))

def kClawSearchCost (k : ℕ) (N1 A : ℝ) (S2 S3 : ℕ) : ℝ :=
  kSeqCost k N1 A (k - 1) S2 + kSeqCost k N1 A k S3

def kClawSearchStandardCost (k : ℕ) (N1 A : ℝ) (S2 S3 : ℕ) : ℝ :=
  kSeqStandardCost k N1 A (k - 1) S2 + kSeqStandardCost k N1 A k S3

theorem kseq_regime1 (k : ℕ) (hk : 2 ≤ k) (N1 A : ℝ) (hN1 : 2 ≤ N1) (hA : 0 < A)
    (hAle : A ≤ N1 ^ k) {q : ℕ} (hq : k - 1 ≤ q) (S : ℕ) :
    kSeqCost k N1 A q S
      ≤ 20 * ((k : ℝ) + 1) ^ 2 * (N1 * A) ^ (1 / ((k : ℝ) + 1)) * Real.log N1 := by
  have hN10 : (0 : ℝ) < N1 := by linarith
  have hlogN : (0 : ℝ) ≤ Real.log N1 := Real.log_nonneg (by linarith)
  have hk1 : 0 < k := by omega
  have hterm : ∀ s ∈ Finset.range S,
      ((s : ℝ) + 1) *
        (if N1 ^ k ≤ A / 2 ^ ((s + 1) * q) then
          kClawDetectCost k (N1 * (A / 2 ^ ((s + 1) * q))) N1
        else
          kClawDetectCost k (N1 * (A / 2 ^ ((s + 1) * q)))
            ((N1 * (A / 2 ^ ((s + 1) * q))) ^ (1 / ((k : ℝ) + 1))))
        ≤ ((s : ℝ) + 1) *
          (((k : ℝ) + 1) ^ 2 * (N1 * A) ^ (1 / ((k : ℝ) + 1)) * (4 / 5 : ℝ) ^ (s + 1)
            * Real.log N1) := by
    intro s _
    set m : ℕ := s + 1
    have hnot : ¬ (N1 ^ k ≤ A / 2 ^ (m * q)) := by
      intro hcon
      have hq1 : 1 ≤ q := by omega
      have hmq : 0 < m * q := Nat.mul_pos (by omega) hq1
      have hle : A / 2 ^ (m * q) < A := div_pow_two_lt_self hA hmq
      have h1 : N1 ^ k < A := lt_of_le_of_lt hcon hle
      linarith
    rw [if_neg hnot]
    set Pm : ℝ := N1 * (A / 2 ^ (m * q)) with hPmdef
    have hPm0 : (0 : ℝ) ≤ Pm := by rw [hPmdef]; positivity
    have hPpos : (0 : ℝ) < Pm := by rw [hPmdef]; positivity
    have hLpos : (0 : ℝ) < Pm ^ (1 / ((k : ℝ) + 1)) := Real.rpow_pos_of_pos hPpos _
    have hLpow : (Pm ^ (1 / ((k : ℝ) + 1))) ^ (k + 1) = Pm :=
      rpow_inv_succ_pow k hk1 hPm0
    have hPle : Pm ≤ N1 ^ (k + 1) := by
      have h1 : A / 2 ^ (m * q) ≤ A := div_pow_two_le_self hA.le (m * q)
      have h2 : N1 * (A / 2 ^ (m * q)) ≤ N1 * A := mul_le_mul_of_nonneg_left h1 hN10.le
      have h3 : N1 * A ≤ N1 * N1 ^ k := mul_le_mul_of_nonneg_left hAle hN10.le
      have h4 : N1 * N1 ^ k = N1 ^ (k + 1) := by rw [pow_succ]; ring
      rw [hPmdef]; linarith
    have hLle : Pm ^ (1 / ((k : ℝ) + 1)) ≤ N1 :=
      le_of_pow_le_pow_left₀ (by omega : k + 1 ≠ 0) hN10.le (by rw [hLpow]; exact hPle)
    have hclaw : kClawDetectCost k Pm (Pm ^ (1 / ((k : ℝ) + 1)))
        ≤ ((k : ℝ) + 1) ^ 2 * Pm ^ (1 / ((k : ℝ) + 1)) * Real.log N1 :=
      kClawDetect_regime1_le (P := Pm) (L := Pm ^ (1 / ((k : ℝ) + 1))) (N1 := N1)
        hk hN1 hLpos hLle hLpow.symm
    have hmaj : Pm ^ (1 / ((k : ℝ) + 1))
        ≤ (N1 * A) ^ (1 / ((k : ℝ) + 1)) * (4 / 5 : ℝ) ^ m := by
      have hPm_eq : Pm = (N1 * A) / 2 ^ (m * q) := by rw [hPmdef]; ring
      rw [hPm_eq]
      exact klevel_regime1_major hk (by positivity : (0 : ℝ) ≤ N1 * A) hq m
    have hcomb : kClawDetectCost k Pm (Pm ^ (1 / ((k : ℝ) + 1)))
        ≤ ((k : ℝ) + 1) ^ 2 * (N1 * A) ^ (1 / ((k : ℝ) + 1)) * (4 / 5 : ℝ) ^ (s + 1)
            * Real.log N1 := by
      calc kClawDetectCost k Pm (Pm ^ (1 / ((k : ℝ) + 1)))
          ≤ ((k : ℝ) + 1) ^ 2 * Pm ^ (1 / ((k : ℝ) + 1)) * Real.log N1 := hclaw
        _ ≤ ((k : ℝ) + 1) ^ 2
              * ((N1 * A) ^ (1 / ((k : ℝ) + 1)) * (4 / 5 : ℝ) ^ m) * Real.log N1 := by
            apply mul_le_mul_of_nonneg_right _ hlogN
            apply mul_le_mul_of_nonneg_left hmaj (by positivity)
        _ = ((k : ℝ) + 1) ^ 2 * (N1 * A) ^ (1 / ((k : ℝ) + 1)) * (4 / 5 : ℝ) ^ (s + 1)
              * Real.log N1 := by
            rw [show m = s + 1 from rfl]; ring
    exact mul_le_mul_of_nonneg_left hcomb (by positivity)
  calc kSeqCost k N1 A q S
      = ∑ s ∈ Finset.range S, ((s : ℝ) + 1) *
        (if N1 ^ k ≤ A / 2 ^ ((s + 1) * q) then
          kClawDetectCost k (N1 * (A / 2 ^ ((s + 1) * q))) N1
        else
          kClawDetectCost k (N1 * (A / 2 ^ ((s + 1) * q)))
            ((N1 * (A / 2 ^ ((s + 1) * q))) ^ (1 / ((k : ℝ) + 1)))) := by rw [kSeqCost]
    _ ≤ ∑ s ∈ Finset.range S, ((s : ℝ) + 1) *
          (((k : ℝ) + 1) ^ 2 * (N1 * A) ^ (1 / ((k : ℝ) + 1)) * (4 / 5 : ℝ) ^ (s + 1)
            * Real.log N1) := Finset.sum_le_sum hterm
    _ = (((k : ℝ) + 1) ^ 2 * (N1 * A) ^ (1 / ((k : ℝ) + 1)) * Real.log N1)
          * ∑ s ∈ Finset.range S, ((s : ℝ) + 1) * (4 / 5 : ℝ) ^ (s + 1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring
    _ ≤ (((k : ℝ) + 1) ^ 2 * (N1 * A) ^ (1 / ((k : ℝ) + 1)) * Real.log N1) * 20 := by
        apply mul_le_mul_of_nonneg_left (weighted_geom_four_fifths_le S)
        positivity
    _ = 20 * ((k : ℝ) + 1) ^ 2 * (N1 * A) ^ (1 / ((k : ℝ) + 1)) * Real.log N1 := by ring

theorem kseq_regime2 (k : ℕ) (hk : 2 ≤ k) (N1 A : ℝ) (hN1 : 2 ≤ N1) (hA : 0 < A)
    (hAk : N1 ^ k ≤ A) {q : ℕ} (hq : k - 1 ≤ q) (S : ℕ) :
    kSeqCost k N1 A q S
      ≤ 20 * ((k : ℝ) + 1) ^ 2 * Real.sqrt (A / N1 ^ (k - 2)) * Real.log N1 := by
  have hN10 : (0 : ℝ) < N1 := by linarith
  have hlogN : (0 : ℝ) ≤ Real.log N1 := Real.log_nonneg (by linarith)
  have hk1 : 0 < k := by omega
  have hterm : ∀ s ∈ Finset.range S,
      ((s : ℝ) + 1) *
        (if N1 ^ k ≤ A / 2 ^ ((s + 1) * q) then
          kClawDetectCost k (N1 * (A / 2 ^ ((s + 1) * q))) N1
        else
          kClawDetectCost k (N1 * (A / 2 ^ ((s + 1) * q)))
            ((N1 * (A / 2 ^ ((s + 1) * q))) ^ (1 / ((k : ℝ) + 1))))
        ≤ ((s : ℝ) + 1) *
          (((k : ℝ) + 1) ^ 2 * Real.sqrt (A / N1 ^ (k - 2)) * (4 / 5 : ℝ) ^ (s + 1)
            * Real.log N1) := by
    intro s _
    set m : ℕ := s + 1
    by_cases hcond : N1 ^ k ≤ A / 2 ^ (m * q)
    · rw [if_pos hcond]
      have hAmpos : (0 : ℝ) < A / 2 ^ (m * q) := by positivity
      have hclaw : kClawDetectCost k (N1 * (A / 2 ^ (m * q))) N1
          ≤ ((k : ℝ) + 1) ^ 2 * Real.sqrt ((A / 2 ^ (m * q)) / N1 ^ (k - 2))
              * Real.log N1 :=
        kClawDetect_regime2_le (k := k) (N1 := N1) (A := A / 2 ^ (m * q))
          hk hN1 hAmpos hcond
      have hX : (0 : ℝ) ≤ A / N1 ^ (k - 2) := by positivity
      have heq : (A / 2 ^ (m * q)) / N1 ^ (k - 2) = (A / N1 ^ (k - 2)) / 2 ^ (m * q) := by
        field_simp
      have hfac : Real.sqrt ((A / 2 ^ (m * q)) / N1 ^ (k - 2))
          = Real.sqrt (A / N1 ^ (k - 2)) * ((2 : ℝ) ^ (-((q : ℝ) * (1/2)))) ^ m := by
        rw [heq, sqrt_div_pow_factor hX q m]
      have hr : ((2 : ℝ) ^ (-((q : ℝ) * (1/2)))) ^ m ≤ (4 / 5 : ℝ) ^ m :=
        pow_le_pow_left₀ (by positivity) (two_rpow_neg_half_le (le_trans (by omega : 1 ≤ k - 1) hq)) m
      have hcomb : kClawDetectCost k (N1 * (A / 2 ^ (m * q))) N1
          ≤ ((k : ℝ) + 1) ^ 2 * Real.sqrt (A / N1 ^ (k - 2)) * (4 / 5 : ℝ) ^ (s + 1)
              * Real.log N1 := by
        calc kClawDetectCost k (N1 * (A / 2 ^ (m * q))) N1
            ≤ ((k : ℝ) + 1) ^ 2 * Real.sqrt ((A / 2 ^ (m * q)) / N1 ^ (k - 2))
                * Real.log N1 := hclaw
          _ = ((k : ℝ) + 1) ^ 2
                * (Real.sqrt (A / N1 ^ (k - 2)) * ((2 : ℝ) ^ (-((q : ℝ) * (1/2)))) ^ m)
                * Real.log N1 := by rw [hfac]
          _ ≤ ((k : ℝ) + 1) ^ 2
                * (Real.sqrt (A / N1 ^ (k - 2)) * (4 / 5 : ℝ) ^ m) * Real.log N1 := by
              apply mul_le_mul_of_nonneg_right _ hlogN
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact mul_le_mul_of_nonneg_left hr (Real.sqrt_nonneg _)
          _ = ((k : ℝ) + 1) ^ 2 * Real.sqrt (A / N1 ^ (k - 2)) * (4 / 5 : ℝ) ^ (s + 1)
                * Real.log N1 := by
              rw [show m = s + 1 from rfl]; ring
      exact mul_le_mul_of_nonneg_left hcomb (by positivity)
    · rw [if_neg hcond]
      have hAlt : A / 2 ^ (m * q) < N1 ^ k := lt_of_not_ge hcond
      set Pm : ℝ := N1 * (A / 2 ^ (m * q)) with hPmdef
      have hPm0 : (0 : ℝ) ≤ Pm := by rw [hPmdef]; positivity
      have hPpos : (0 : ℝ) < Pm := by rw [hPmdef]; positivity
      have hLpos : (0 : ℝ) < Pm ^ (1 / ((k : ℝ) + 1)) := Real.rpow_pos_of_pos hPpos _
      have hLpow : (Pm ^ (1 / ((k : ℝ) + 1))) ^ (k + 1) = Pm :=
        rpow_inv_succ_pow k hk1 hPm0
      have hPle : Pm ≤ N1 ^ (k + 1) := by
        have h2 : N1 * (A / 2 ^ (m * q)) ≤ N1 * N1 ^ k :=
          mul_le_mul_of_nonneg_left hAlt.le hN10.le
        have h4 : N1 * N1 ^ k = N1 ^ (k + 1) := by rw [pow_succ]; ring
        rw [hPmdef]; linarith
      have hLle : Pm ^ (1 / ((k : ℝ) + 1)) ≤ N1 :=
        le_of_pow_le_pow_left₀ (by omega : k + 1 ≠ 0) hN10.le (by rw [hLpow]; exact hPle)
      have hclaw : kClawDetectCost k Pm (Pm ^ (1 / ((k : ℝ) + 1)))
          ≤ ((k : ℝ) + 1) ^ 2 * Pm ^ (1 / ((k : ℝ) + 1)) * Real.log N1 :=
        kClawDetect_regime1_le (P := Pm) (L := Pm ^ (1 / ((k : ℝ) + 1))) (N1 := N1)
          hk hN1 hLpos hLle hLpow.symm
      have hmaj : Pm ^ (1 / ((k : ℝ) + 1))
          ≤ (N1 * A) ^ (1 / ((k : ℝ) + 1)) * (4 / 5 : ℝ) ^ m := by
        have hPm_eq : Pm = (N1 * A) / 2 ^ (m * q) := by rw [hPmdef]; ring
        rw [hPm_eq]
        exact klevel_regime1_major hk (by positivity : (0 : ℝ) ≤ N1 * A) hq m
      have hbase : (N1 * A) ^ (1 / ((k : ℝ) + 1)) ≤ Real.sqrt (A / N1 ^ (k - 2)) :=
        klevel_base_le_regime2 hk hN10 hA hAk
      have hLbound : Pm ^ (1 / ((k : ℝ) + 1))
          ≤ Real.sqrt (A / N1 ^ (k - 2)) * (4 / 5 : ℝ) ^ m :=
        le_trans hmaj (mul_le_mul_of_nonneg_right hbase (by positivity))
      have hcomb : kClawDetectCost k Pm (Pm ^ (1 / ((k : ℝ) + 1)))
          ≤ ((k : ℝ) + 1) ^ 2 * Real.sqrt (A / N1 ^ (k - 2)) * (4 / 5 : ℝ) ^ (s + 1)
              * Real.log N1 := by
        calc kClawDetectCost k Pm (Pm ^ (1 / ((k : ℝ) + 1)))
            ≤ ((k : ℝ) + 1) ^ 2 * Pm ^ (1 / ((k : ℝ) + 1)) * Real.log N1 := hclaw
          _ ≤ ((k : ℝ) + 1) ^ 2
                * (Real.sqrt (A / N1 ^ (k - 2)) * (4 / 5 : ℝ) ^ m) * Real.log N1 := by
              apply mul_le_mul_of_nonneg_right _ hlogN
              exact mul_le_mul_of_nonneg_left hLbound (by positivity)
          _ = ((k : ℝ) + 1) ^ 2 * Real.sqrt (A / N1 ^ (k - 2)) * (4 / 5 : ℝ) ^ (s + 1)
                * Real.log N1 := by
              rw [show m = s + 1 from rfl]; ring
      exact mul_le_mul_of_nonneg_left hcomb (by positivity)
  calc kSeqCost k N1 A q S
      = ∑ s ∈ Finset.range S, ((s : ℝ) + 1) *
        (if N1 ^ k ≤ A / 2 ^ ((s + 1) * q) then
          kClawDetectCost k (N1 * (A / 2 ^ ((s + 1) * q))) N1
        else
          kClawDetectCost k (N1 * (A / 2 ^ ((s + 1) * q)))
            ((N1 * (A / 2 ^ ((s + 1) * q))) ^ (1 / ((k : ℝ) + 1)))) := by rw [kSeqCost]
    _ ≤ ∑ s ∈ Finset.range S, ((s : ℝ) + 1) *
          (((k : ℝ) + 1) ^ 2 * Real.sqrt (A / N1 ^ (k - 2)) * (4 / 5 : ℝ) ^ (s + 1)
            * Real.log N1) := Finset.sum_le_sum hterm
    _ = (((k : ℝ) + 1) ^ 2 * Real.sqrt (A / N1 ^ (k - 2)) * Real.log N1)
          * ∑ s ∈ Finset.range S, ((s : ℝ) + 1) * (4 / 5 : ℝ) ^ (s + 1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring
    _ ≤ (((k : ℝ) + 1) ^ 2 * Real.sqrt (A / N1 ^ (k - 2)) * Real.log N1) * 20 := by
        apply mul_le_mul_of_nonneg_left (weighted_geom_four_fifths_le S)
        positivity
    _ = 20 * ((k : ℝ) + 1) ^ 2 * Real.sqrt (A / N1 ^ (k - 2)) * Real.log N1 := by ring

theorem kseqStandard_regime1 (k : ℕ) (hk : 2 ≤ k) (N1 A : ℝ) (hN1 : 2 ≤ N1) (hA : 0 < A)
    (hAle : A ≤ N1 ^ k) {q : ℕ} (hq : k - 1 ≤ q) (S : ℕ) :
    kSeqStandardCost k N1 A q S
      ≤ 20 * ((k : ℝ) + 1) * (N1 * A) ^ (1 / ((k : ℝ) + 1)) := by
  have hN10 : (0 : ℝ) < N1 := by linarith
  have hk1 : 0 < k := by omega
  have hterm : ∀ s ∈ Finset.range S,
      ((s : ℝ) + 1) *
        (if N1 ^ k ≤ A / 2 ^ ((s + 1) * q) then
          kClawDetectStandardCost k (N1 * (A / 2 ^ ((s + 1) * q))) N1
        else
          kClawDetectStandardCost k (N1 * (A / 2 ^ ((s + 1) * q)))
            ((N1 * (A / 2 ^ ((s + 1) * q))) ^ (1 / ((k : ℝ) + 1))))
        ≤ ((s : ℝ) + 1) *
          (((k : ℝ) + 1) * (N1 * A) ^ (1 / ((k : ℝ) + 1)) * (4 / 5 : ℝ) ^ (s + 1)) := by
    intro s _
    set m : ℕ := s + 1
    have hnot : ¬ (N1 ^ k ≤ A / 2 ^ (m * q)) := by
      intro hcon
      have hq1 : 1 ≤ q := by omega
      have hmq : 0 < m * q := Nat.mul_pos (by omega) hq1
      have hle : A / 2 ^ (m * q) < A := div_pow_two_lt_self hA hmq
      have h1 : N1 ^ k < A := lt_of_le_of_lt hcon hle
      linarith
    rw [if_neg hnot]
    set Pm : ℝ := N1 * (A / 2 ^ (m * q)) with hPmdef
    have hPm0 : (0 : ℝ) ≤ Pm := by rw [hPmdef]; positivity
    have hPpos : (0 : ℝ) < Pm := by rw [hPmdef]; positivity
    have hLpos : (0 : ℝ) < Pm ^ (1 / ((k : ℝ) + 1)) := Real.rpow_pos_of_pos hPpos _
    have hLpow : (Pm ^ (1 / ((k : ℝ) + 1))) ^ (k + 1) = Pm :=
      rpow_inv_succ_pow k hk1 hPm0
    have hPle : Pm ≤ N1 ^ (k + 1) := by
      have h1 : A / 2 ^ (m * q) ≤ A := div_pow_two_le_self hA.le (m * q)
      have h2 : N1 * (A / 2 ^ (m * q)) ≤ N1 * A := mul_le_mul_of_nonneg_left h1 hN10.le
      have h3 : N1 * A ≤ N1 * N1 ^ k := mul_le_mul_of_nonneg_left hAle hN10.le
      have h4 : N1 * N1 ^ k = N1 ^ (k + 1) := by rw [pow_succ]; ring
      rw [hPmdef]; linarith
    have hLle : Pm ^ (1 / ((k : ℝ) + 1)) ≤ N1 :=
      le_of_pow_le_pow_left₀ (by omega : k + 1 ≠ 0) hN10.le (by rw [hLpow]; exact hPle)
    have hclaw : kClawDetectStandardCost k Pm (Pm ^ (1 / ((k : ℝ) + 1)))
        ≤ ((k : ℝ) + 1) * Pm ^ (1 / ((k : ℝ) + 1)) :=
      kClawDetectStandard_regime1_le (P := Pm) (L := Pm ^ (1 / ((k : ℝ) + 1)))
        (N1 := N1) hk hN1 hLpos hLle hLpow.symm
    have hmaj : Pm ^ (1 / ((k : ℝ) + 1))
        ≤ (N1 * A) ^ (1 / ((k : ℝ) + 1)) * (4 / 5 : ℝ) ^ m := by
      have hPm_eq : Pm = (N1 * A) / 2 ^ (m * q) := by rw [hPmdef]; ring
      rw [hPm_eq]
      exact klevel_regime1_major hk (by positivity : (0 : ℝ) ≤ N1 * A) hq m
    have hcomb : kClawDetectStandardCost k Pm (Pm ^ (1 / ((k : ℝ) + 1)))
        ≤ ((k : ℝ) + 1) * (N1 * A) ^ (1 / ((k : ℝ) + 1)) * (4 / 5 : ℝ) ^ (s + 1) := by
      calc kClawDetectStandardCost k Pm (Pm ^ (1 / ((k : ℝ) + 1)))
          ≤ ((k : ℝ) + 1) * Pm ^ (1 / ((k : ℝ) + 1)) := hclaw
        _ ≤ ((k : ℝ) + 1) * ((N1 * A) ^ (1 / ((k : ℝ) + 1)) * (4 / 5 : ℝ) ^ m) := by
            exact mul_le_mul_of_nonneg_left hmaj (by positivity)
        _ = ((k : ℝ) + 1) * (N1 * A) ^ (1 / ((k : ℝ) + 1)) * (4 / 5 : ℝ) ^ (s + 1) := by
            rw [show m = s + 1 from rfl]; ring
    exact mul_le_mul_of_nonneg_left hcomb (by positivity)
  calc kSeqStandardCost k N1 A q S
      = ∑ s ∈ Finset.range S, ((s : ℝ) + 1) *
        (if N1 ^ k ≤ A / 2 ^ ((s + 1) * q) then
          kClawDetectStandardCost k (N1 * (A / 2 ^ ((s + 1) * q))) N1
        else
          kClawDetectStandardCost k (N1 * (A / 2 ^ ((s + 1) * q)))
            ((N1 * (A / 2 ^ ((s + 1) * q))) ^ (1 / ((k : ℝ) + 1)))) := by rw [kSeqStandardCost]
    _ ≤ ∑ s ∈ Finset.range S, ((s : ℝ) + 1) *
          (((k : ℝ) + 1) * (N1 * A) ^ (1 / ((k : ℝ) + 1)) * (4 / 5 : ℝ) ^ (s + 1)) :=
        Finset.sum_le_sum hterm
    _ = (((k : ℝ) + 1) * (N1 * A) ^ (1 / ((k : ℝ) + 1)))
          * ∑ s ∈ Finset.range S, ((s : ℝ) + 1) * (4 / 5 : ℝ) ^ (s + 1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring
    _ ≤ (((k : ℝ) + 1) * (N1 * A) ^ (1 / ((k : ℝ) + 1))) * 20 := by
        apply mul_le_mul_of_nonneg_left (weighted_geom_four_fifths_le S)
        positivity
    _ = 20 * ((k : ℝ) + 1) * (N1 * A) ^ (1 / ((k : ℝ) + 1)) := by ring

theorem kseqStandard_regime2 (k : ℕ) (hk : 2 ≤ k) (N1 A : ℝ) (hN1 : 2 ≤ N1) (hA : 0 < A)
    (hAk : N1 ^ k ≤ A) {q : ℕ} (hq : k - 1 ≤ q) (S : ℕ) :
    kSeqStandardCost k N1 A q S
      ≤ 20 * ((k : ℝ) + 1) * Real.sqrt (A / N1 ^ (k - 2)) := by
  have hN10 : (0 : ℝ) < N1 := by linarith
  have hk1 : 0 < k := by omega
  have hterm : ∀ s ∈ Finset.range S,
      ((s : ℝ) + 1) *
        (if N1 ^ k ≤ A / 2 ^ ((s + 1) * q) then
          kClawDetectStandardCost k (N1 * (A / 2 ^ ((s + 1) * q))) N1
        else
          kClawDetectStandardCost k (N1 * (A / 2 ^ ((s + 1) * q)))
            ((N1 * (A / 2 ^ ((s + 1) * q))) ^ (1 / ((k : ℝ) + 1))))
        ≤ ((s : ℝ) + 1) *
          (((k : ℝ) + 1) * Real.sqrt (A / N1 ^ (k - 2)) * (4 / 5 : ℝ) ^ (s + 1)) := by
    intro s _
    set m : ℕ := s + 1
    by_cases hcond : N1 ^ k ≤ A / 2 ^ (m * q)
    · rw [if_pos hcond]
      have hAmpos : (0 : ℝ) < A / 2 ^ (m * q) := by positivity
      have hclaw : kClawDetectStandardCost k (N1 * (A / 2 ^ (m * q))) N1
          ≤ ((k : ℝ) + 1) * Real.sqrt ((A / 2 ^ (m * q)) / N1 ^ (k - 2)) :=
        kClawDetectStandard_regime2_le (k := k) (N1 := N1) (A := A / 2 ^ (m * q))
          hk hN1 hAmpos hcond
      have hX : (0 : ℝ) ≤ A / N1 ^ (k - 2) := by positivity
      have heq : (A / 2 ^ (m * q)) / N1 ^ (k - 2) = (A / N1 ^ (k - 2)) / 2 ^ (m * q) := by
        field_simp
      have hfac : Real.sqrt ((A / 2 ^ (m * q)) / N1 ^ (k - 2))
          = Real.sqrt (A / N1 ^ (k - 2)) * ((2 : ℝ) ^ (-((q : ℝ) * (1/2)))) ^ m := by
        rw [heq, sqrt_div_pow_factor hX q m]
      have hr : ((2 : ℝ) ^ (-((q : ℝ) * (1/2)))) ^ m ≤ (4 / 5 : ℝ) ^ m :=
        pow_le_pow_left₀ (by positivity) (two_rpow_neg_half_le (le_trans (by omega : 1 ≤ k - 1) hq)) m
      have hcomb : kClawDetectStandardCost k (N1 * (A / 2 ^ (m * q))) N1
          ≤ ((k : ℝ) + 1) * Real.sqrt (A / N1 ^ (k - 2)) * (4 / 5 : ℝ) ^ (s + 1) := by
        calc kClawDetectStandardCost k (N1 * (A / 2 ^ (m * q))) N1
            ≤ ((k : ℝ) + 1) * Real.sqrt ((A / 2 ^ (m * q)) / N1 ^ (k - 2)) := hclaw
          _ = ((k : ℝ) + 1)
                * (Real.sqrt (A / N1 ^ (k - 2)) * ((2 : ℝ) ^ (-((q : ℝ) * (1/2)))) ^ m) := by
              rw [hfac]
          _ ≤ ((k : ℝ) + 1) * (Real.sqrt (A / N1 ^ (k - 2)) * (4 / 5 : ℝ) ^ m) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hr (Real.sqrt_nonneg _)) (by positivity)
          _ = ((k : ℝ) + 1) * Real.sqrt (A / N1 ^ (k - 2)) * (4 / 5 : ℝ) ^ (s + 1) := by
              rw [show m = s + 1 from rfl]; ring
      exact mul_le_mul_of_nonneg_left hcomb (by positivity)
    · rw [if_neg hcond]
      have hAlt : A / 2 ^ (m * q) < N1 ^ k := lt_of_not_ge hcond
      set Pm : ℝ := N1 * (A / 2 ^ (m * q)) with hPmdef
      have hPm0 : (0 : ℝ) ≤ Pm := by rw [hPmdef]; positivity
      have hPpos : (0 : ℝ) < Pm := by rw [hPmdef]; positivity
      have hLpos : (0 : ℝ) < Pm ^ (1 / ((k : ℝ) + 1)) := Real.rpow_pos_of_pos hPpos _
      have hLpow : (Pm ^ (1 / ((k : ℝ) + 1))) ^ (k + 1) = Pm :=
        rpow_inv_succ_pow k hk1 hPm0
      have hPle : Pm ≤ N1 ^ (k + 1) := by
        have h2 : N1 * (A / 2 ^ (m * q)) ≤ N1 * N1 ^ k :=
          mul_le_mul_of_nonneg_left hAlt.le hN10.le
        have h4 : N1 * N1 ^ k = N1 ^ (k + 1) := by rw [pow_succ]; ring
        rw [hPmdef]; linarith
      have hLle : Pm ^ (1 / ((k : ℝ) + 1)) ≤ N1 :=
        le_of_pow_le_pow_left₀ (by omega : k + 1 ≠ 0) hN10.le (by rw [hLpow]; exact hPle)
      have hclaw : kClawDetectStandardCost k Pm (Pm ^ (1 / ((k : ℝ) + 1)))
          ≤ ((k : ℝ) + 1) * Pm ^ (1 / ((k : ℝ) + 1)) :=
        kClawDetectStandard_regime1_le (P := Pm) (L := Pm ^ (1 / ((k : ℝ) + 1)))
          (N1 := N1) hk hN1 hLpos hLle hLpow.symm
      have hmaj : Pm ^ (1 / ((k : ℝ) + 1))
          ≤ (N1 * A) ^ (1 / ((k : ℝ) + 1)) * (4 / 5 : ℝ) ^ m := by
        have hPm_eq : Pm = (N1 * A) / 2 ^ (m * q) := by rw [hPmdef]; ring
        rw [hPm_eq]
        exact klevel_regime1_major hk (by positivity : (0 : ℝ) ≤ N1 * A) hq m
      have hbase : (N1 * A) ^ (1 / ((k : ℝ) + 1)) ≤ Real.sqrt (A / N1 ^ (k - 2)) :=
        klevel_base_le_regime2 hk hN10 hA hAk
      have hLbound : Pm ^ (1 / ((k : ℝ) + 1))
          ≤ Real.sqrt (A / N1 ^ (k - 2)) * (4 / 5 : ℝ) ^ m :=
        le_trans hmaj (mul_le_mul_of_nonneg_right hbase (by positivity))
      have hcomb : kClawDetectStandardCost k Pm (Pm ^ (1 / ((k : ℝ) + 1)))
          ≤ ((k : ℝ) + 1) * Real.sqrt (A / N1 ^ (k - 2)) * (4 / 5 : ℝ) ^ (s + 1) := by
        calc kClawDetectStandardCost k Pm (Pm ^ (1 / ((k : ℝ) + 1)))
            ≤ ((k : ℝ) + 1) * Pm ^ (1 / ((k : ℝ) + 1)) := hclaw
          _ ≤ ((k : ℝ) + 1) * (Real.sqrt (A / N1 ^ (k - 2)) * (4 / 5 : ℝ) ^ m) := by
              exact mul_le_mul_of_nonneg_left hLbound (by positivity)
          _ = ((k : ℝ) + 1) * Real.sqrt (A / N1 ^ (k - 2)) * (4 / 5 : ℝ) ^ (s + 1) := by
              rw [show m = s + 1 from rfl]; ring
      exact mul_le_mul_of_nonneg_left hcomb (by positivity)
  calc kSeqStandardCost k N1 A q S
      = ∑ s ∈ Finset.range S, ((s : ℝ) + 1) *
        (if N1 ^ k ≤ A / 2 ^ ((s + 1) * q) then
          kClawDetectStandardCost k (N1 * (A / 2 ^ ((s + 1) * q))) N1
        else
          kClawDetectStandardCost k (N1 * (A / 2 ^ ((s + 1) * q)))
            ((N1 * (A / 2 ^ ((s + 1) * q))) ^ (1 / ((k : ℝ) + 1)))) := by rw [kSeqStandardCost]
    _ ≤ ∑ s ∈ Finset.range S, ((s : ℝ) + 1) *
          (((k : ℝ) + 1) * Real.sqrt (A / N1 ^ (k - 2)) * (4 / 5 : ℝ) ^ (s + 1)) :=
        Finset.sum_le_sum hterm
    _ = (((k : ℝ) + 1) * Real.sqrt (A / N1 ^ (k - 2)))
          * ∑ s ∈ Finset.range S, ((s : ℝ) + 1) * (4 / 5 : ℝ) ^ (s + 1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring
    _ ≤ (((k : ℝ) + 1) * Real.sqrt (A / N1 ^ (k - 2))) * 20 := by
        apply mul_le_mul_of_nonneg_left (weighted_geom_four_fifths_le S)
        positivity
    _ = 20 * ((k : ℝ) + 1) * Real.sqrt (A / N1 ^ (k - 2)) := by ring

theorem theorem10_kClawFinding_regime1 (k : ℕ) (hk : 2 ≤ k) (N1 A : ℝ) (hN1 : 2 ≤ N1) (hA : 0 < A)
    (hAle : A ≤ N1 ^ k) (S2 S3 : ℕ) :
    kClawSearchCost k N1 A S2 S3
      ≤ 64 * ((k : ℝ) + 1) ^ 2 * (N1 * A) ^ (1 / ((k : ℝ) + 1)) * Real.log N1 := by
  have h2 := kseq_regime1 k hk N1 A hN1 hA hAle (le_refl (k - 1)) S2
  have h3 := kseq_regime1 k hk N1 A hN1 hA hAle (by omega : k - 1 ≤ k) S3
  have hlogN : (0 : ℝ) ≤ Real.log N1 := Real.log_nonneg (by linarith)
  have hX : (0 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 * (N1 * A) ^ (1 / ((k : ℝ) + 1)) * Real.log N1 :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by positivity) _)) hlogN
  rw [kClawSearchCost]
  nlinarith [h2, h3, hX]

theorem theorem10_kClawFinding_regime2 (k : ℕ) (hk : 2 ≤ k) (N1 A : ℝ) (hN1 : 2 ≤ N1) (hA : 0 < A)
    (hAk : N1 ^ k ≤ A) (S2 S3 : ℕ) :
    kClawSearchCost k N1 A S2 S3
      ≤ 64 * ((k : ℝ) + 1) ^ 2 * Real.sqrt (A / N1 ^ (k - 2)) * Real.log N1 := by
  have h2 := kseq_regime2 k hk N1 A hN1 hA hAk (le_refl (k - 1)) S2
  have h3 := kseq_regime2 k hk N1 A hN1 hA hAk (by omega : k - 1 ≤ k) S3
  have hlogN : (0 : ℝ) ≤ Real.log N1 := Real.log_nonneg (by linarith)
  have hX : (0 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 * Real.sqrt (A / N1 ^ (k - 2)) * Real.log N1 :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)) hlogN
  rw [kClawSearchCost]
  nlinarith [h2, h3, hX]

theorem corollary11_kClawFinding_regime1 (k : ℕ) (hk : 2 ≤ k) (N1 A : ℝ) (hN1 : 2 ≤ N1) (hA : 0 < A)
    (hAle : A ≤ N1 ^ k) (S2 S3 : ℕ) :
    kClawSearchStandardCost k N1 A S2 S3
      ≤ 64 * ((k : ℝ) + 1) * (N1 * A) ^ (1 / ((k : ℝ) + 1)) := by
  have h2 := kseqStandard_regime1 k hk N1 A hN1 hA hAle (le_refl (k - 1)) S2
  have h3 := kseqStandard_regime1 k hk N1 A hN1 hA hAle (by omega : k - 1 ≤ k) S3
  have hX : (0 : ℝ) ≤ ((k : ℝ) + 1) * (N1 * A) ^ (1 / ((k : ℝ) + 1)) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
  rw [kClawSearchStandardCost]
  nlinarith [h2, h3, hX]

theorem corollary11_kClawFinding_regime2 (k : ℕ) (hk : 2 ≤ k) (N1 A : ℝ) (hN1 : 2 ≤ N1) (hA : 0 < A)
    (hAk : N1 ^ k ≤ A) (S2 S3 : ℕ) :
    kClawSearchStandardCost k N1 A S2 S3
      ≤ 64 * ((k : ℝ) + 1) * Real.sqrt (A / N1 ^ (k - 2)) := by
  have h2 := kseqStandard_regime2 k hk N1 A hN1 hA hAk (le_refl (k - 1)) S2
  have h3 := kseqStandard_regime2 k hk N1 A hN1 hA hAk (by omega : k - 1 ≤ k) S3
  have hX : (0 : ℝ) ≤ ((k : ℝ) + 1) * Real.sqrt (A / N1 ^ (k - 2)) :=
    mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  rw [kClawSearchStandardCost]
  nlinarith [h2, h3, hX]

end Qatlib.Papers.ClawFinding07.MainResults.QueryBound
