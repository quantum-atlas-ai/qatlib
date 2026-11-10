/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.RankCost
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

noncomputable def binaryLog (x : ℝ) : ℝ := Real.log x / Real.log 2

noncomputable def sourceMeanBudget (N : ℕ) : ℝ :=
  (45 / 4 : ℝ) * Real.sqrt N + (7 / 10 : ℝ) * (binaryLog N) ^ 2

noncomputable def sourceTimeout (N : ℕ) : ℝ :=
  (45 / 2 : ℝ) * Real.sqrt N + (7 / 5 : ℝ) * (binaryLog N) ^ 2

theorem sourceTimeout_eq_twice (N : ℕ) : sourceTimeout N = 2 * sourceMeanBudget N := by
  unfold sourceTimeout sourceMeanBudget
  ring

theorem sourceMeanBudget_pos (N : ℕ) (hN : 0 < N) : 0 < sourceMeanBudget N := by
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hN)
  unfold sourceMeanBudget
  nlinarith [sq_nonneg (binaryLog N)]

theorem sqrtCost_step (r : ℕ) (hr : 0 < r) :
    1 / (((r : ℝ) + 1) * Real.sqrt r) ≤
      2 * (1 / Real.sqrt r - 1 / Real.sqrt ((r : ℝ) + 1)) := by
  have hrr : (0 : ℝ) < r := by exact_mod_cast hr
  have ha : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.2 hrr
  have hb : 0 < Real.sqrt ((r : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  have ha2 := Real.sq_sqrt hrr.le
  have hb2 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (r : ℝ) + 1)
  have hden : (((r : ℝ) + 1) * Real.sqrt r) =
      Real.sqrt ((r : ℝ) + 1) ^ 2 * Real.sqrt r := by rw [hb2]
  rw [hden]
  apply (div_le_iff₀ (by positivity : 0 < Real.sqrt ((r : ℝ) + 1) ^ 2 * Real.sqrt r)).2
  have heq : (2 * (1 / Real.sqrt r - 1 / Real.sqrt ((r : ℝ) + 1))) *
      (Real.sqrt ((r : ℝ) + 1) ^ 2 * Real.sqrt r) =
      2 * Real.sqrt ((r : ℝ) + 1) ^ 2 -
        2 * Real.sqrt (r : ℝ) * Real.sqrt ((r : ℝ) + 1) := by
    field_simp
  rw [heq]
  nlinarith [sq_nonneg (Real.sqrt (r : ℝ) - Real.sqrt ((r : ℝ) + 1))]

theorem sqrtCost_sum (n : ℕ) :
    (∑ k ∈ Finset.range n, 1 / (((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 1))) ≤ 2 := by
  have ht (m : ℕ) : (∑ k ∈ Finset.range m,
      1 / (((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 1))) ≤
      2 * (1 - 1 / Real.sqrt ((m : ℝ) + 1)) := by
    induction m with
    | zero => norm_num
    | succ m ih =>
      have hstep := sqrtCost_step (m + 1) (by omega)
      push_cast at hstep ⊢
      rw [Finset.sum_range_succ]
      have heq : (m : ℝ) + 1 + 1 = (m : ℝ) + 2 := by ring
      rw [heq] at hstep ⊢
      linarith
  have hp : 0 ≤ 1 / Real.sqrt ((n : ℝ) + 1) := by positivity
  linarith [ht n]

theorem harmonic_tail (n : ℕ) :
    (∑ k ∈ Finset.range n, (1 : ℝ) / ((k : ℝ) + 2)) = (harmonic (n + 1) : ℝ) - 1 := by
  induction n with
  | zero => norm_num [harmonic]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, harmonic_succ (n + 1)]
    push_cast
    ring

theorem initialization_sum (N : ℕ) (hN : 0 < N) :
    (∑ k ∈ Finset.range (N - 1), binaryLog N / ((k : ℝ) + 2)) ≤
      (7 / 10 : ℝ) * (binaryLog N) ^ 2 := by
  unfold binaryLog
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  let L := Real.log (n + 1 : ℕ) / Real.log 2
  have hlog : 0 ≤ Real.log (n + 1 : ℕ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n + 1))
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 ≤ L := div_nonneg hlog h2.le
  have hH : (∑ k ∈ Finset.range n, (1 : ℝ) / ((k : ℝ) + 2)) ≤
      Real.log (n + 1 : ℕ) := by
    rw [harmonic_tail]
    linarith [harmonic_le_one_add_log (n + 1)]
  have heq : Real.log (n + 1 : ℕ) * L = Real.log 2 * L ^ 2 := by
    dsimp [L]
    field_simp
  have hlog2 : Real.log 2 ≤ (7 / 10 : ℝ) := by linarith [Real.log_two_lt_d9]
  change (∑ k ∈ Finset.range n, L / ((k : ℝ) + 2)) ≤ (7 / 10 : ℝ) * L ^ 2
  calc
    _ = L * (∑ k ∈ Finset.range n, (1 : ℝ) / ((k : ℝ) + 2)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ L * Real.log (n + 1 : ℕ) := mul_le_mul_of_nonneg_left hH hL
    _ = Real.log 2 * L ^ 2 := by nlinarith [heq]
    _ ≤ _ := mul_le_mul_of_nonneg_right hlog2 (sq_nonneg L)

theorem source_clock_sum (N : ℕ) (hN : 0 < N) :
    (∑ k ∈ Finset.range (N - 1),
      ((9 / 2 : ℝ) * Real.sqrt ((N : ℝ) / ((k : ℝ) + 1)) + binaryLog N) /
        ((k : ℝ) + 2)) ≤ sourceMeanBudget N := by
  have heach (k : ℕ) :
      ((9 / 2 : ℝ) * Real.sqrt ((N : ℝ) / ((k : ℝ) + 1))) / ((k : ℝ) + 2) =
      ((9 / 2 : ℝ) * Real.sqrt N) *
        (1 / (((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 1))) := by
    rw [Real.sqrt_div (Nat.cast_nonneg N)]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  simp_rw [add_div, heach]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hgrover := mul_le_mul_of_nonneg_left (sqrtCost_sum (N - 1))
    (by positivity : 0 ≤ (9 / 2 : ℝ) * Real.sqrt N)
  have hinit := initialization_sum N hN
  have hs := Real.sqrt_nonneg (N : ℝ)
  unfold sourceMeanBudget
  linarith

theorem expectedTraceCost_le_sourceMeanBudget (N : ℕ) (hN : 0 < N) (cost : ℕ → ℝ)
    (hstop : cost 1 = 0)
    (hcost : ∀ r, 2 ≤ r → r ≤ N → cost r ≤
      (9 / 2 : ℝ) * Real.sqrt ((N : ℝ) / ((r : ℝ) - 1)) + binaryLog N) :
    expectedTraceCost cost N ≤ sourceMeanBudget N := by
  have hbudget := source_clock_sum N hN
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  rw [expectedTraceCost_sum, Finset.sum_range_succ']
  simp only [Nat.zero_add, hstop, zero_div, add_zero]
  apply le_trans _ hbudget
  apply Finset.sum_le_sum
  intro k hk
  have hkN : k + 2 ≤ n + 1 := by have := Finset.mem_range.mp hk; omega
  have h := hcost (k + 2) (by omega) hkN
  push_cast at h ⊢
  have heq : (k : ℝ) + 2 - 1 = (k : ℝ) + 1 := by ring
  rw [heq] at h
  have hn : (k : ℝ) + 1 + 1 = (k : ℝ) + 2 := by ring
  rw [hn]
  exact div_le_div_of_nonneg_right h (by positivity)

end Qatlib.Concepts.AmplitudeSearch.Amplification
