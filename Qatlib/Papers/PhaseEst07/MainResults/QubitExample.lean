/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PhaseEst07.MainResults.Shared.PathShift
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PhaseEst07.MainResults.QubitExample

open scoped BigOperators
open Qatlib.Papers.PhaseEst07.MainResults.Shared

noncomputable def sourceQubitAmplitude (N : ℕ) (a b : ℝ) (k : ℕ) : ℝ :=
  Real.sqrt (Nat.choose N k : ℝ) * a ^ (N - k) * b ^ k

noncomputable def sourceQubitCost (N : ℕ) (a b : ℝ) : ℝ :=
  (1 - ∑ k ∈ Finset.range N,
      sourceQubitAmplitude N a b k * sourceQubitAmplitude N a b (k + 1)) / 2

noncomputable def sourceQubitMinCost (N : ℕ) : ℝ :=
  (1 : ℝ) / 2 -
    (1 / (2 : ℝ) ^ (N + 1)) *
      ∑ k ∈ Finset.range N,
        Real.sqrt ((Nat.choose N k : ℝ) * (Nat.choose N (k + 1) : ℝ))

theorem source_qubit_symmetric_dim (N : ℕ) : (N + 1) = N + 1 := rfl

theorem source_qubit_binomial_sum (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), (Nat.choose N k : ℝ) = (2 : ℝ) ^ N := by
  rw [← Nat.cast_sum, Nat.sum_range_choose]
  push_cast
  ring

theorem source_qubit_cost_balanced (N : ℕ) :
    sourceQubitCost N (1 / Real.sqrt 2) (1 / Real.sqrt 2) = sourceQubitMinCost N := by
  set r : ℝ := 1 / Real.sqrt 2 with hr
  have hr2 : r ^ 2 = 1 / 2 := by
    rw [hr, div_pow, Real.sq_sqrt (by norm_num)]
    norm_num

  have hS : (∑ k ∈ Finset.range N,
        sourceQubitAmplitude N r r k * sourceQubitAmplitude N r r (k + 1))
      = (1 / 2) ^ N *
          ∑ k ∈ Finset.range N,
            Real.sqrt ((Nat.choose N k : ℝ) * (Nat.choose N (k + 1) : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkN : k ≤ N := le_of_lt (Finset.mem_range.mp hk)
    have hk1N : k + 1 ≤ N := by have := Finset.mem_range.mp hk; omega
    have hA : (0 : ℝ) ≤ (Nat.choose N k : ℝ) := by positivity
    have hsqrt : Real.sqrt (Nat.choose N k : ℝ) * Real.sqrt (Nat.choose N (k + 1) : ℝ)
        = Real.sqrt ((Nat.choose N k : ℝ) * (Nat.choose N (k + 1) : ℝ)) :=
      (Real.sqrt_mul hA _).symm
    have hpow1 : r ^ (N - k) * r ^ k = r ^ N := by
      rw [← pow_add, Nat.sub_add_cancel hkN]
    have hpow2 : r ^ (N - (k + 1)) * r ^ (k + 1) = r ^ N := by
      rw [← pow_add, Nat.sub_add_cancel hk1N]
    have hrN : r ^ N * r ^ N = (1 / 2) ^ N := by
      rw [← pow_add, show N + N = 2 * N by ring, pow_mul, hr2]
    calc sourceQubitAmplitude N r r k * sourceQubitAmplitude N r r (k + 1)
        = (Real.sqrt (Nat.choose N k : ℝ) * Real.sqrt (Nat.choose N (k + 1) : ℝ)) *
            ((r ^ (N - k) * r ^ k) * (r ^ (N - (k + 1)) * r ^ (k + 1))) := by
            unfold sourceQubitAmplitude
            ring
      _ = Real.sqrt ((Nat.choose N k : ℝ) * (Nat.choose N (k + 1) : ℝ)) *
            (r ^ N * r ^ N) := by
            rw [hsqrt, hpow1, hpow2]
      _ = (1 / 2) ^ N *
            Real.sqrt ((Nat.choose N k : ℝ) * (Nat.choose N (k + 1) : ℝ)) := by
            rw [hrN, mul_comm]
  unfold sourceQubitCost sourceQubitMinCost
  rw [hS, one_div_pow, pow_succ]
  ring

theorem source_qubit_amplitude_sq (N : ℕ) (a b : ℝ) (k : ℕ) :
    (sourceQubitAmplitude N a b k) ^ 2
      = (Nat.choose N k : ℝ) * (a ^ 2) ^ (N - k) * (b ^ 2) ^ k := by
  unfold sourceQubitAmplitude
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  have h2 : (a ^ (N - k)) ^ 2 = (a ^ 2) ^ (N - k) := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have h3 : (b ^ k) ^ 2 = (b ^ 2) ^ k := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [h2, h3]

theorem source_qubit_sq_sum (N : ℕ) (a b : ℝ) :
    ∑ k ∈ Finset.range (N + 1), (sourceQubitAmplitude N a b k) ^ 2
      = (a ^ 2 + b ^ 2) ^ N := by
  have hbin := add_pow (b ^ 2) (a ^ 2) N
  rw [add_comm (b ^ 2) (a ^ 2)] at hbin
  rw [hbin]
  apply Finset.sum_congr rfl
  intro k _
  rw [source_qubit_amplitude_sq]
  ring

theorem source_qubit_normalized (N : ℕ) (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    ∑ k ∈ Finset.range (N + 1), (sourceQubitAmplitude N a b k) ^ 2 = 1 := by
  rw [source_qubit_sq_sum, h, one_pow]

theorem source_qubit_correlation_le_cos (N : ℕ) (hN : 1 ≤ N) (a b : ℝ)
    (h : a ^ 2 + b ^ 2 = 1) :
    ∑ k ∈ Finset.range N,
        sourceQubitAmplitude N a b k * sourceQubitAmplitude N a b (k + 1)
      ≤ Real.cos (Real.pi / ((N + 2 : ℕ) : ℝ)) := by
  have hm : 0 < N + 1 := by omega
  have hp := path_shift_le (N + 1) hm (sourceQubitAmplitude N a b)
  have hnorm := source_qubit_normalized N a b h
  have hcos : Real.cos (theta (N + 1))
      = Real.cos (Real.pi / ((N + 2 : ℕ) : ℝ)) := by
    unfold theta
    congr 1
    push_cast
    ring
  have hN1 : N + 1 - 1 = N := by omega
  rw [hcos, hN1, hnorm, mul_one] at hp
  simpa using hp

theorem source_qubit_optimal_one (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    sourceQubitCost 1 a b ≥ sourceQubitMinCost 1 := by
  have hcost : sourceQubitCost 1 a b = (1 - a * b) / 2 := by
    unfold sourceQubitCost sourceQubitAmplitude
    rw [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num [Nat.choose]
  have hmin : sourceQubitMinCost 1 = 1 / 4 := by
    unfold sourceQubitMinCost
    rw [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num [Nat.choose]
  rw [hcost, hmin]
  have hab : a * b ≤ 1 / 2 := by nlinarith [sq_nonneg (a - b)]
  linarith

theorem source_qubit_optimal_two (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    sourceQubitCost 2 a b ≥ sourceQubitMinCost 2 := by
  have hcost : sourceQubitCost 2 a b = (1 - Real.sqrt 2 * (a * b)) / 2 := by
    unfold sourceQubitCost sourceQubitAmplitude
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num [Nat.choose]
    have hsq : a ^ 2 * (Real.sqrt 2 * a * b) + Real.sqrt 2 * a * b * b ^ 2
        = Real.sqrt 2 * (a * b) * (a ^ 2 + b ^ 2) := by ring
    rw [hsq, h, mul_one]
  have hmin : sourceQubitMinCost 2 = (1 - Real.sqrt 2 / 2) / 2 := by
    unfold sourceQubitMinCost
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num [Nat.choose]
    ring
  rw [hcost, hmin]
  have hab : a * b ≤ 1 / 2 := by nlinarith [sq_nonneg (a - b)]
  have hs : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith

end Qatlib.Papers.PhaseEst07.MainResults.QubitExample
