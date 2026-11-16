/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GevreyGrad19.MainResults.Model.GevreyGradDefinitions
public import Qatlib.Concepts.GradientOracle.CentralDiff.CentralDifferencePowerSumBoundOpti
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section


/-!
# Complete central-difference source bounds

Bridges the public binomial-coefficient model to arXiv:1909.13528v1,
Definition 3.3 and Theorem 3.4, without extra mathematical assumptions.
-/

set_option autoImplicit false
open scoped BigOperators
open Qatlib.Papers.GevreyGrad19.MainResults
open Qatlib.Concepts.GradientOracle.CentralDiff

namespace Qatlib.Papers.GevreyGrad19.MainResults

/-- The exponential suppression in the central-difference bound dominates its square-root prefactor. -/
theorem suppression_bound (m : ℕ) (hm : 2 ≤ m) :
    6 * Real.exp (-(7 / 6 : ℝ) * m) * Real.sqrt m ≤ 2 := by
  have hmr : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hnonneg : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hs : (Real.sqrt m) ^ 2 = (m : ℝ) := Real.sq_sqrt hnonneg
  have hsbound : Real.sqrt m ≤ ((m : ℝ) + 1) / 2 := by
    nlinarith [sq_nonneg (Real.sqrt m - 1)]
  have hquad : 3 * (((m : ℝ) + 1) / 2) ≤ ((7 / 12 : ℝ) * m + 1) ^ 2 := by
    nlinarith [sq_nonneg ((m : ℝ) - 2)]
  have hexp : ((7 / 12 : ℝ) * m + 1) ^ 2 ≤ Real.exp ((7 / 6 : ℝ) * m) := by
    have h := Real.add_one_le_exp ((7 / 12 : ℝ) * m)
    have hn : (0 : ℝ) ≤ (7 / 12 : ℝ) * m + 1 := by positivity
    calc
      _ ≤ (Real.exp ((7 / 12 : ℝ) * m)) ^ 2 := pow_le_pow_left₀ hn h 2
      _ = Real.exp ((7 / 6 : ℝ) * m) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
  have hlarge : 3 * Real.sqrt m ≤ Real.exp ((7 / 6 : ℝ) * m) := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hlarge
    (le_of_lt (Real.exp_pos (-(7 / 6 : ℝ) * m)))
  have heq : Real.exp (-(7 / 6 : ℝ) * m) * Real.exp ((7 / 6 : ℝ) * m) = 1 := by
    rw [← Real.exp_add, show -(7 / 6 : ℝ) * m + (7 / 6 : ℝ) * m = 0 by ring,
      Real.exp_zero]
  nlinarith

/-- High-order moments of the paper coefficients satisfy the source bound via the public absolute-moment estimate. -/
theorem paper_power_sum_bound (m k : ℕ) (hm : 2 ≤ m) (hk : 2 * m + 1 ≤ k) :
    |∑ ℓ ∈ Finset.Ico (-(m : ℤ)) ((m : ℤ) + 1), paperCentralCoeff m ℓ * (ℓ : ℝ) ^ k| ≤
      2 * (m : ℝ) ^ k := by
  have hm0 : 0 < m := by omega
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm0
  have hk0 : 1 ≤ k := by omega
  have hkp : k - 1 + 1 = k := by omega
  have hb := centralDifferencePowerSumBound m (k - 1) hm0 (by omega)
  rw [hkp] at hb
  have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub hk0, Nat.cast_one]
  have hp : (m : ℝ) ^ (((k - 1 : ℕ) : ℝ) + 3 / 2) =
      (m : ℝ) ^ k * Real.sqrt m := by
    rw [hcast]
    have he : (k : ℝ) - 1 + 3 / 2 = (k : ℝ) + 1 / 2 := by ring
    rw [he, Real.rpow_add hmr, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  have hcoeff : ∀ ℓ : ℤ,
      paperCentralCoeff m ℓ * (ℓ : ℝ) ^ k = centralDiffCoeff m ℓ * (ℓ : ℝ) ^ k := by
    intro ℓ
    by_cases hℓ : ℓ = 0
    · subst ℓ
      simp [paperCentralCoeff, centralDiffCoeff, show k ≠ 0 by omega]
    · simp [paperCentralCoeff, hℓ]
  calc
    _ = |∑ ℓ ∈ Finset.Ico (-(m : ℤ)) ((m : ℤ) + 1),
        centralDiffCoeff m ℓ * (ℓ : ℝ) ^ k| := by simp_rw [hcoeff]
    _ ≤ ∑ ℓ ∈ Finset.Ico (-(m : ℤ)) ((m : ℤ) + 1),
        |centralDiffCoeff m ℓ * (ℓ : ℝ) ^ k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ 6 * Real.exp (-(7 / 6 : ℝ) * m) *
        (m : ℝ) ^ (((k - 1 : ℕ) : ℝ) + 3 / 2) := hb
    _ = (6 * Real.exp (-(7 / 6 : ℝ) * m) * Real.sqrt m) * (m : ℝ) ^ k := by
      rw [hp]
      ring
    _ ≤ 2 * (m : ℝ) ^ k :=
      mul_le_mul_of_nonneg_right (suppression_bound m hm) (by positivity)


end Qatlib.Papers.GevreyGrad19.MainResults
