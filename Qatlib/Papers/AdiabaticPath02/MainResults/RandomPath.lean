/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabaticPath02.MainResults.SymmetricDefs
import Mathlib.Topology.Order.Basic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AdiabaticPath02.MainResults.RandomPath

open Qatlib.Papers.AdiabaticPath02.MainResults.PathDefs
open Qatlib.Papers.AdiabaticPath02.MainResults.SymmetricDefs
open scoped BigOperators

theorem polynomial_schedule_bound {C c : ℝ} {a q : ℕ}
    (hC : 0 < C) (hc : 0 < c) (n : ℕ) (hn : 1 ≤ n) :
    C * (n : ℝ) ^ a / (c / (n : ℝ) ^ q) ^ 2 =
      (C / c ^ 2) * (n : ℝ) ^ (a + 2 * q) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hnq : (n : ℝ) ^ q ≠ 0 := pow_ne_zero _ (ne_of_gt hn0)
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc0
  have hnq2 : ((n : ℝ) ^ q) ^ 2 ≠ 0 := pow_ne_zero 2 hnq
  rw [div_pow]
  field_simp
  rw [pow_add, pow_mul, ← pow_mul, ← pow_mul, Nat.mul_comm q 2]

theorem polynomial_schedule_exists (C c : ℝ) (a q : ℕ) (hC : 0 < C) (hc : 0 < c) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ n : ℕ, 1 ≤ n →
      C * (n : ℝ) ^ a / (c / (n : ℝ) ^ q) ^ 2 ≤
        C' * ((n : ℝ) + 1) ^ (a + 2 * q) := by
  have hC' : 0 < C / c ^ 2 + 1 := by
    have hpos : 0 < C / c ^ 2 := div_pos hC (pow_pos hc 2)
    linarith
  refine ⟨C / c ^ 2 + 1, hC', fun n hn => ?_⟩
  rw [polynomial_schedule_bound hC hc n hn]
  have hcoef : C / c ^ 2 ≤ C / c ^ 2 + 1 := le_add_of_nonneg_right zero_le_one
  have hbase : (n : ℝ) ≤ (n : ℝ) + 1 := le_add_of_nonneg_right zero_le_one
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hpow : (n : ℝ) ^ (a + 2 * q) ≤ ((n : ℝ) + 1) ^ (a + 2 * q) :=
    pow_le_pow_left₀ hn0 hbase _
  exact mul_le_mul hcoef hpow (pow_nonneg hn0 _) hC'.le

noncomputable def scheduleCeil (C' : ℝ) (d : ℕ) : ℕ → ℕ :=
  fun n => Nat.ceil (C' * ((n : ℝ) + 1) ^ d)

theorem scheduleCeil_isPolynomialBound (C' : ℝ) (hC' : 0 < C') (d : ℕ) :
    IsPolynomialBound (scheduleCeil C' d) := by
  refine ⟨Nat.ceil (C' + 1) + 1, d, Nat.succ_pos _, fun n => ?_⟩
  unfold scheduleCeil
  have hmain : (Nat.ceil (C' * ((n : ℝ) + 1) ^ d) : ℝ) ≤
      ((Nat.ceil (C' + 1) + 1 : ℕ) : ℝ) * ((n : ℝ) + 1) ^ d := by
    have hx0 : 0 ≤ C' * ((n : ℝ) + 1) ^ d := by positivity
    have hceil := (Nat.ceil_lt_add_one hx0).le
    have hC'' : C' + 1 ≤ ((Nat.ceil (C' + 1) + 1 : ℕ) : ℝ) := by
      have h1 := Nat.le_ceil (C' + 1)
      have h2 : ((Nat.ceil (C' + 1) : ℕ) : ℝ) ≤ ((Nat.ceil (C' + 1) + 1 : ℕ) : ℝ) := by
        push_cast; linarith
      linarith
    have hpow1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ d := by
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
      exact one_le_pow₀ this
    calc (Nat.ceil (C' * ((n : ℝ) + 1) ^ d) : ℝ)
        ≤ C' * ((n : ℝ) + 1) ^ d + 1 := hceil
      _ ≤ (C' + 1) * ((n : ℝ) + 1) ^ d := by nlinarith
      _ ≤ ((Nat.ceil (C' + 1) + 1 : ℕ) : ℝ) * ((n : ℝ) + 1) ^ d := by
          have hpow0 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ d := by positivity
          exact mul_le_mul_of_nonneg_right hC'' hpow0
  exact_mod_cast hmain

theorem polynomial_schedule_nat (C c : ℝ) (a q : ℕ) (hC : 0 < C) (hc : 0 < c) :
    ∃ T : ℕ → ℕ, IsPolynomialBound T ∧
      ∀ n : ℕ, 1 ≤ n →
        C * (n : ℝ) ^ a / (c / (n : ℝ) ^ q) ^ 2 ≤ (T n : ℝ) := by
  obtain ⟨C', hC', hC'b⟩ := polynomial_schedule_exists C c a q hC hc
  refine ⟨scheduleCeil C' (a + 2 * q), scheduleCeil_isPolynomialBound C' hC' _, ?_⟩
  intro n hn
  refine (hC'b n hn).trans ?_
  exact Nat.le_ceil _

theorem source_A28_is_legal_sample :
    IsP2Sample (sourceA28.map (fun z : ℤ => (z : ℝ))) :=
  sourceA28_isP2Sample

theorem source_ground_state_minimises_cost (n : ℕ) :
    cost n (fun _ => false) = 0 ∧ ∀ z : Fin n → Bool, 0 ≤ cost n z :=
  cost_all_zero_is_global_min n

theorem source_hp_ground_energy_zero (n : ℕ) :
    hpEnergy (n : ℝ) 0 = 0 ∧
      ∀ k : Fin (n + 1), 0 ≤ hpEnergy (n : ℝ) (k.val : ℝ) := by
  constructor
  · exact hpEnergy_zero (n : ℝ)
  · intro k
    exact hpEnergy_nonneg_nat (Nat.le_of_lt_succ k.isLt)

def StraightPathFails (T : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop, straightFidelity n (T n) < 1 - ε

theorem source_random_path_components :
    IsP2Sample (sourceA28.map (fun z : ℤ => (z : ℝ))) ∧
      (∀ n : ℕ, cost n (fun _ => false) = 0 ∧ ∀ z : Fin n → Bool, 0 ≤ cost n z) ∧
      (∀ n : ℕ, hpEnergy (n : ℝ) 0 = 0 ∧
        ∀ k : Fin (n + 1), 0 ≤ hpEnergy (n : ℝ) (k.val : ℝ)) ∧
      (∀ C c : ℝ, ∀ a q : ℕ, 0 < C → 0 < c →
        ∃ T : ℕ → ℕ, IsPolynomialBound T ∧
          ∀ n : ℕ, 1 ≤ n → C * (n : ℝ) ^ a / (c / (n : ℝ) ^ q) ^ 2 ≤ (T n : ℝ)) ∧
      (∀ (n T : ℕ),
        evolutionOperator (p2Scheduled n (T : ℝ)) (T : ℝ) ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ) :=
  ⟨sourceA28_isP2Sample, source_ground_state_minimises_cost, source_hp_ground_energy_zero,
    polynomial_schedule_nat,
    fun n T => evolutionOperator_unitary n (T : ℝ)⟩

end Qatlib.Papers.AdiabaticPath02.MainResults.RandomPath
