/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsRefinedDefs
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.DiracEquation16.GateCost

open Qatlib.Concepts.ResourceBounds.AsymBounds (uniformUpperBound)
set_option warningAsError false

def perAxisCostModel (na : ℕ) : ℕ := na * na

def stepCostModel (K nx ny nz : ℕ) : ℕ :=
  perAxisCostModel nx + perAxisCostModel ny + perAxisCostModel nz + K

def cubicCostModel (K n : ℕ) : ℕ := stepCostModel K n n n

def latticePoints (nx ny nz : ℕ) : ℕ := 2 ^ nx * 2 ^ ny * 2 ^ nz

def classicalModel (nx ny nz : ℕ) : ℕ := latticePoints nx ny nz

def cubicClassicalModel (n : ℕ) : ℕ := classicalModel n n n

theorem cubicCostModel_eq (K n : ℕ) :
    cubicCostModel K n = 3 * n * n + K := by
  unfold cubicCostModel stepCostModel perAxisCostModel
  ring

theorem cubicClassicalModel_eq (n : ℕ) :
    cubicClassicalModel n = 8 ^ n := by
  unfold cubicClassicalModel classicalModel latticePoints
  rw [← mul_pow, ← mul_pow]
  norm_num

theorem classicalModel_is_linear (nx ny nz : ℕ) :
    classicalModel nx ny nz = latticePoints nx ny nz := rfl

theorem cubicCostModel_poly (K n : ℕ) :
    cubicCostModel K n ≤ (K + 3) * (n + 1) ^ 2 := by
  rw [cubicCostModel_eq]
  have hA : 3 * n * n ≤ (K + 3) * (n * n) := by
    have h := Nat.mul_le_mul_right (n * n) (by omega : 3 ≤ K + 3)
    simpa [mul_assoc, mul_comm, mul_left_comm] using! h
  have hB : K ≤ K + 3 := by omega
  have h1 : 3 * n * n + K ≤ (K + 3) * (n * n) + (K + 3) :=
    Nat.add_le_add hA hB
  have he : (K + 3) * (n * n) + (K + 3) = (K + 3) * (n * n + 1) := by ring
  have h2 : n * n + 1 ≤ (n + 1) ^ 2 := by
    have e : (n + 1) ^ 2 = n * n + 2 * n + 1 := by ring
    rw [e]; omega
  calc 3 * n * n + K ≤ (K + 3) * (n * n) + (K + 3) := h1
    _ = (K + 3) * (n * n + 1) := he
    _ ≤ (K + 3) * (n + 1) ^ 2 := Nat.mul_le_mul_left (K + 3) h2

theorem cubicCostModel_uniformUpperBound (K : ℕ) :
    uniformUpperBound (fun n => cubicCostModel K n) (K + 3) 2 := by
  intro n
  simpa [pow_two] using! cubicCostModel_poly K n

theorem exists_poly_lt_pow (C d : ℕ) {b : ℕ} (hb : 1 < b) :
    ∃ N : ℕ, ∀ n ≥ N, (C : ℝ) * ((n : ℝ) + 1) ^ d < (b : ℝ) ^ n := by
  rcases Nat.eq_zero_or_pos C with hC | hCpos_nat
  · refine ⟨0, ?_⟩
    intro n _
    subst hC
    have : (0 : ℝ) < (b : ℝ) ^ n := by positivity
    simpa using! this
  have hCpos : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hCpos_nat
  have hbR : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb

  have hlim : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ d / (b : ℝ) ^ n)
      Filter.atTop (nhds 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt d hbR

  set D : ℝ := (C : ℝ) * (b : ℝ) ^ d + 1 with hDdef
  have hDpos : 0 < D := by rw [hDdef]; positivity
  have hε : (0 : ℝ) < 1 / D := by positivity
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) ^ d / (b : ℝ) ^ n < 1 / D :=
    hlim.eventually (isOpen_Iio.mem_nhds hε)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N0, hN0⟩ := hev
  refine ⟨max N0 1, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hmain := hN0 n (le_trans (le_max_left _ _) hn)

  have hKpos : (0 : ℝ) < (C : ℝ) * (2 : ℝ) ^ d := by positivity
  have hpow : (2 : ℝ) ^ d ≤ (b : ℝ) ^ d := by
    have h2b : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast (by omega : 2 ≤ b)
    exact pow_le_pow_left₀ (by norm_num) h2b d
  have hKD : (C : ℝ) * (2 : ℝ) ^ d < D := by
    have hC0 : (0 : ℝ) ≤ (C : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left hpow hC0
    rw [hDdef]; nlinarith

  have hKsmall : (C : ℝ) * (2 : ℝ) ^ d * (1 / D) < 1 := by
    rw [mul_one_div, div_lt_one hDpos]
    exact hKD
  have hstep : (C : ℝ) * (2 : ℝ) ^ d * ((n : ℝ) ^ d / (b : ℝ) ^ n) < 1 := by
    have hm := mul_lt_mul_of_pos_left hmain hKpos
    linarith [hm, hKsmall]
  have hbnpos : (0 : ℝ) < (b : ℝ) ^ n := by positivity
  have hKey : (C : ℝ) * (2 : ℝ) ^ d * (n : ℝ) ^ d < (b : ℝ) ^ n := by
    have heq : (C : ℝ) * (2 : ℝ) ^ d * ((n : ℝ) ^ d / (b : ℝ) ^ n) =
        ((C : ℝ) * (2 : ℝ) ^ d * (n : ℝ) ^ d) / (b : ℝ) ^ n := by ring
    rw [heq, div_lt_one hbnpos] at hstep
    exact hstep

  have hle : ((n : ℝ) + 1) ^ d ≤ (2 * (n : ℝ)) ^ d :=
    pow_le_pow_left₀ (by positivity) (by linarith) d
  have hpoly : (C : ℝ) * ((n : ℝ) + 1) ^ d ≤
      (C : ℝ) * (2 : ℝ) ^ d * (n : ℝ) ^ d := by
    calc (C : ℝ) * ((n : ℝ) + 1) ^ d ≤ (C : ℝ) * (2 * (n : ℝ)) ^ d :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = (C : ℝ) * (2 : ℝ) ^ d * (n : ℝ) ^ d := by rw [mul_pow]; ring
  linarith

theorem one_dimensional_separation (C d : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, (C : ℝ) * ((n : ℝ) + 1) ^ d < (2 : ℝ) ^ n :=
  exists_poly_lt_pow C d (by norm_num)

theorem three_dimensional_separation (C d : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, (C : ℝ) * ((n : ℝ) + 1) ^ d < (8 : ℝ) ^ n :=
  exists_poly_lt_pow C d (by norm_num)

theorem modeled_speedup_unbounded (B C d : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, (B * C : ℝ) * ((n : ℝ) + 1) ^ d < (8 : ℝ) ^ n := by
  simpa [Nat.cast_mul] using! exists_poly_lt_pow (B * C) d (b := 8) (by norm_num)

theorem modeled_iterated_speedup_unbounded (Nt B C d : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N,
      (Nt * B * C : ℝ) * ((n : ℝ) + 1) ^ d < (8 : ℝ) ^ n := by
  simpa [Nat.cast_mul] using! exists_poly_lt_pow (Nt * B * C) d (b := 8) (by norm_num)

end Qatlib.Papers.DiracEquation16.GateCost
