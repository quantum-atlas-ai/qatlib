/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.FermionicSim00.MainResults

theorem state_preparation_success_probability {N : ℕ} (_hN : 0 < N) (a : Fin N → ℂ)
    (ha : ∑ α, ‖a α‖ ^ 2 = 1) :
    (∑ α, ‖a α‖ ^ 2) / (N : ℝ) = 1 / (N : ℝ) := by
  rw [ha]

theorem expected_trials_eq (N : ℕ) (hN : 2 ≤ N) :
    ∑' k : ℕ, ((k : ℝ) + 1) * ((1 : ℝ) - 1 / (N : ℝ)) ^ k * (1 / (N : ℝ)) = (N : ℝ) := by
  set r : ℝ := 1 - 1 / (N : ℝ) with hrdef
  set p : ℝ := 1 / (N : ℝ) with hpdef
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hp0 : 0 < p := by rw [hpdef]; positivity
  have hp_le_one : p ≤ 1 := by
    rw [hpdef, div_le_iff₀ hNpos]
    simpa using hN1
  have hr0 : 0 ≤ r := by rw [hrdef]; linarith
  have hr1 : r < 1 := by rw [hrdef]; linarith
  have h1 : ∑' k : ℕ, r ^ k = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0 hr1
  have hnorm : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1
  have h2 : ∑' k : ℕ, (k : ℝ) * r ^ k = r / (1 - r) ^ 2 :=
    tsum_coe_mul_geometric_of_norm_lt_one hnorm
  have hs1 : Summable (fun k : ℕ => (k : ℝ) * r ^ k) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
  have hs0 : Summable (fun k : ℕ => r ^ k) := summable_geometric_of_norm_lt_one hnorm
  have hsum : ∑' k : ℕ, ((k : ℝ) + 1) * r ^ k = (1 - r)⁻¹ + r / (1 - r) ^ 2 := by
    have hsplit : (fun k : ℕ => ((k : ℝ) + 1) * r ^ k)
        = fun k : ℕ => (k : ℝ) * r ^ k + r ^ k := by
      funext k; ring
    rw [hsplit, Summable.tsum_add hs1 hs0, h2, h1]
    exact add_comm _ _
  have hpr : 1 - r = p := by rw [hrdef]; ring
  have hkey : (1 - r)⁻¹ + r / (1 - r) ^ 2 = 1 / p ^ 2 := by
    rw [hpr]
    field_simp
    ring
  have hgoal : ∑' k : ℕ, ((k : ℝ) + 1) * r ^ k * p = (1 / p ^ 2) * p := by
    rw [tsum_mul_right, hsum, hkey]
  calc ∑' k : ℕ, ((k : ℝ) + 1) * r ^ k * p
      = (1 / p ^ 2) * p := hgoal
    _ = 1 / p := by field_simp
    _ = (N : ℝ) := by
        rw [hpdef]
        field_simp

theorem construction_cost_le (N n Ne : ℕ) (hNe : Ne ≤ 2 * n) :
    N ^ 2 * n * Ne ≤ 2 * (N ^ 2 * n ^ 2) := by
  have h1 : N ^ 2 * n * Ne ≤ N ^ 2 * n * (2 * n) := Nat.mul_le_mul_left _ hNe
  calc N ^ 2 * n * Ne ≤ N ^ 2 * n * (2 * n) := h1
    _ = 2 * (N ^ 2 * n ^ 2) := by ring

theorem construction_cost_le_of_le (N n Ne : ℕ) (hNe : Ne ≤ n) :
    N ^ 2 * n * Ne ≤ N ^ 2 * n ^ 2 := by
  have h1 : N ^ 2 * n * Ne ≤ N ^ 2 * n * n := Nat.mul_le_mul_left _ hNe
  calc N ^ 2 * n * Ne ≤ N ^ 2 * n * n := h1
    _ = N ^ 2 * n ^ 2 := by ring

theorem construction_cost_polynomial (N n Ne k : ℕ) (hN : N ≤ n ^ k) (hNe : Ne ≤ 2 * n) :
    N ^ 2 * n * Ne ≤ 2 * n ^ (2 * k + 2) := by
  have hbase : N ^ 2 ≤ n ^ (2 * k) := by
    calc N ^ 2 ≤ (n ^ k) ^ 2 := Nat.pow_le_pow_left hN 2
      _ = n ^ (2 * k) := by rw [← pow_mul]; ring_nf
  have hmid : N ^ 2 * n * Ne ≤ (n ^ (2 * k)) * n * (2 * n) := by
    refine Nat.mul_le_mul (Nat.mul_le_mul hbase le_rfl) hNe
  calc N ^ 2 * n * Ne ≤ (n ^ (2 * k)) * n * (2 * n) := hmid
    _ = 2 * n ^ (2 * k + 2) := by
        rw [pow_add]
        ring

end Qatlib.Papers.FermionicSim00.MainResults
