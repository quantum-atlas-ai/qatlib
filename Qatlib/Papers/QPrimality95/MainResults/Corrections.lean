/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CostRecurrences.FiniteWeights
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.QPrimality95.MainResults

def logCounterPrimes : Finset ℕ := {11,13,17,19,23,29,31,37}

theorem logCounterPrimes_prime : ∀ p ∈ logCounterPrimes, p.Prime := by
  norm_num [logCounterPrimes]

theorem double_log_sum_counterexample :
    Real.log (Real.log (∏ p ∈ logCounterPrimes, (p : ℝ))) <
      ∑ p ∈ logCounterPrimes, Real.log (Real.log (p : ℝ)) := by
  have hlo : ∀ p ∈ logCounterPrimes, (11 : ℝ) ≤ p := by
    intro p hp
    simp only [logCounterPrimes, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hpos : ∀ p ∈ logCounterPrimes, (0 : ℝ) < p :=
      fun p hp => lt_of_lt_of_le (by norm_num) (hlo p hp)
  have he : Real.exp (2 : ℝ) < 11 := by
    have ht := Real.exp_one_lt_three
    have h0 := Real.exp_pos (1 : ℝ)
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith
  have hlogp : ∀ p ∈ logCounterPrimes, (2 : ℝ) ≤ Real.log p := by
    intro p hp
    exact (Real.le_log_iff_exp_le (hpos p hp)).mpr (he.le.trans (hlo p hp))
  have hu : Real.log (∏ p ∈ logCounterPrimes, (p : ℝ)) < (2 : ℝ) ^ 8 := by
    calc
      _ ≤ ∑ p ∈ logCounterPrimes, ((p : ℝ) - 1) :=
        Qatlib.Foundations.CostRecurrences.FiniteWeights.log_prod_le_sum_sub_one _ _ hpos
      _ < _ := by norm_num [logCounterPrimes]
  have hp : 0 < Real.log (∏ p ∈ logCounterPrimes, (p : ℝ)) := by
    apply Real.log_pos
    norm_num [logCounterPrimes]
  have hr : Real.log (Real.log (∏ p ∈ logCounterPrimes, (p : ℝ))) < 8 * Real.log 2 := by
    have h := Real.log_lt_log hp hu
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hl : 8 * Real.log 2 ≤ ∑ p ∈ logCounterPrimes, Real.log (Real.log (p : ℝ)) := by
    calc
      _ = ∑ _p ∈ logCounterPrimes, Real.log (2 : ℝ) := by norm_num [logCounterPrimes]
      _ ≤ _ := Finset.sum_le_sum (fun p hp => Real.log_le_log (by norm_num) (hlogp p hp))
  exact hr.trans_le hl

theorem sum_log_le_log_of_factorization {N : ℕ} (S : Finset ℕ) (β : ℕ → ℕ)
    (hprime : ∀ p ∈ S, p.Prime) (hβ : ∀ p ∈ S, 0 < β p)
    (hN : N = ∏ p ∈ S, p ^ β p) :
    (∑ p ∈ S, Real.log (p : ℝ)) ≤ Real.log (N : ℝ) := by
  subst hN
  rw [Nat.cast_prod]
  rw [Real.log_prod]
  · apply Finset.sum_le_sum
    intro p hp
    push_cast
    rw [Real.log_pow]
    have hppos : (0 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (hprime p hp).pos.le
    have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by
      exact_mod_cast (hprime p hp).one_le)
    have hβ1 : (1 : ℝ) ≤ (β p : ℝ) := by
      exact_mod_cast hβ p hp
    have h := mul_le_mul_of_nonneg_left hβ1 hlog
    simpa [mul_comm] using h
  · intro p hp
    push_cast
    exact pow_ne_zero _ (by exact_mod_cast (hprime p hp).ne_zero)

theorem sum_cube_log_le_cube_log_of_factorization {N : ℕ} (S : Finset ℕ) (β : ℕ → ℕ)
    (hprime : ∀ p ∈ S, p.Prime) (hβ : ∀ p ∈ S, 0 < β p)
    (hN : N = ∏ p ∈ S, p ^ β p) :
    (∑ p ∈ S, Real.log (p : ℝ) ^ 3) ≤ Real.log (N : ℝ) ^ 3 := by
  have hnonneg : ∀ p ∈ S, 0 ≤ Real.log (p : ℝ) := by
    intro p hp
    exact Real.log_nonneg (by exact_mod_cast (hprime p hp).one_le)
  have h4a := sum_log_le_log_of_factorization S β hprime hβ hN
  calc (∑ p ∈ S, Real.log (p : ℝ) ^ 3)
      ≤ (∑ p ∈ S, Real.log (p : ℝ)) ^ 3 :=
        Qatlib.Foundations.CostRecurrences.FiniteWeights.sum_cube_le_cube_sum
          S (fun p => Real.log (p : ℝ)) hnonneg
    _ ≤ Real.log (N : ℝ) ^ 3 :=
        pow_le_pow_left₀ (Finset.sum_nonneg hnonneg) h4a 3

end Qatlib.Papers.QPrimality95.MainResults
