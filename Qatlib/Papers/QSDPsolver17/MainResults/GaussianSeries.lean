/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QSDPsolver17.MainResults.Gaussian
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Tactic.FieldSimp

@[expose] public section


/-! # A summable uniform envelope for every Gaussian derivative. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QSDPsolver17.MainResults.Gaussian
/-- A uniform envelope removes the argument from the Gaussian derivative estimate at positive orders. -/
theorem envelope_uniform (k : ℕ) (hk : 1 ≤ k) (t : ℝ) (ht : 0 ≤ t) :
    (2 * t + 2 * (k : ℝ)) ^ k * Real.exp (-(t ^ 2)) ≤ (4 * (k : ℝ)) ^ k := by
  have he0 : 0 ≤ Real.exp (-(t ^ 2)) := (Real.exp_pos _).le
  have he1 : Real.exp (-(t ^ 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])
  by_cases htk : t ≤ (k : ℝ)
  · have hbase : 2 * t + 2 * (k : ℝ) ≤ 4 * (k : ℝ) := by linarith
    calc (2 * t + 2 * (k : ℝ)) ^ k * Real.exp (-(t ^ 2))
        ≤ (4 * (k : ℝ)) ^ k * 1 :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) hbase k) he1 he0 (by positivity)
      _ = _ := mul_one _
  · have hkt : (k : ℝ) ≤ t := (lt_of_not_ge htk).le
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have htpos : 0 < t := by linarith
    have hlog : Real.log t ≤ t := by linarith [Real.log_le_sub_one_of_pos htpos]
    have hlogpow : (k : ℝ) * Real.log t ≤ t ^ 2 := by
      calc (k : ℝ) * Real.log t ≤ (k : ℝ) * t :=
          mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
        _ ≤ t * t := mul_le_mul_of_nonneg_right hkt ht
        _ = t ^ 2 := by ring
    have hpow : t ^ k ≤ Real.exp (t ^ 2) := by
      calc t ^ k = Real.exp (Real.log (t ^ k)) := (Real.exp_log (pow_pos htpos _)).symm
        _ = Real.exp ((k : ℝ) * Real.log t) := by rw [Real.log_pow]
        _ ≤ Real.exp (t ^ 2) := Real.exp_le_exp.mpr hlogpow
    have hkernel : t ^ k * Real.exp (-(t ^ 2)) ≤ (k : ℝ) ^ k := by
      calc t ^ k * Real.exp (-(t ^ 2))
          ≤ Real.exp (t ^ 2) * Real.exp (-(t ^ 2)) :=
            mul_le_mul_of_nonneg_right hpow he0
        _ = 1 := by rw [← Real.exp_add]; simp
        _ ≤ (k : ℝ) ^ k := one_le_pow₀ hk1
    calc (2 * t + 2 * (k : ℝ)) ^ k * Real.exp (-(t ^ 2))
        ≤ (4 * t) ^ k * Real.exp (-(t ^ 2)) := by
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (by positivity) (by linarith) _) he0
      _ = 4 ^ k * (t ^ k * Real.exp (-(t ^ 2))) := by rw [mul_pow]; ring
      _ ≤ 4 ^ k * (k : ℝ) ^ k := mul_le_mul_of_nonneg_left hkernel (by positivity)
      _ = (4 * (k : ℝ)) ^ k := (mul_pow _ _ _).symm

/-- Each factorial-weighted derivative is dominated by the corresponding geometric term. -/
theorem gaussian_term_bound (x : ℝ) (k : ℕ) :
    |iteratedDeriv k expNegSq x| / (k.factorial : ℝ) *
        (1 / (8 * Real.exp 1)) ^ k ≤ (1 / 2 : ℝ) ^ k := by
  cases k with
  | zero =>
      simpa [iteratedDeriv_zero, expNegSq, abs_of_pos (Real.exp_pos _)] using
        (Real.exp_le_one_iff.mpr (show -(x ^ 2) ≤ 0 by nlinarith [sq_nonneg x]))
  | succ n =>
      let k := n + 1
      have hk : 1 ≤ k := by dsimp [k]; omega
      have hbound : |iteratedDeriv k expNegSq x| ≤ (4 * (k : ℝ)) ^ k := by
        have henv := envelope_uniform k hk |x| (abs_nonneg x)
        rw [sq_abs] at henv
        exact (lemma45_deriv_bound k x).trans henv
      have hfact : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
      have hpow : (k : ℝ) ^ k / (k.factorial : ℝ) ≤ Real.exp 1 ^ k := by
        simpa only [← Real.exp_nat_mul, mul_one] using
          Real.pow_div_factorial_le_exp (k : ℝ) (Nat.cast_nonneg (α := ℝ) k) k
      change |iteratedDeriv k expNegSq x| / (k.factorial : ℝ) *
        (1 / (8 * Real.exp 1)) ^ k ≤ (1 / 2 : ℝ) ^ k
      calc |iteratedDeriv k expNegSq x| / (k.factorial : ℝ) * (1 / (8 * Real.exp 1)) ^ k
          ≤ (4 * (k : ℝ)) ^ k / (k.factorial : ℝ) * (1 / (8 * Real.exp 1)) ^ k :=
            mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hbound hfact.le) (by positivity)
        _ = 4 ^ k * ((k : ℝ) ^ k / (k.factorial : ℝ)) * (1 / (8 * Real.exp 1)) ^ k := by
            rw [mul_pow]
            ring
        _ ≤ 4 ^ k * (Real.exp 1 ^ k) * (1 / (8 * Real.exp 1)) ^ k := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
        _ = (4 * Real.exp 1 * (1 / (8 * Real.exp 1))) ^ k := by
            rw [mul_pow, mul_pow]
        _ = (1 / 2 : ℝ) ^ k := by
            congr 1
            field_simp [Real.exp_ne_zero]
            ring

/-- Lemma 45, Eq. (23): the absolutely weighted derivative series is bounded by two. -/
theorem lemma45_series_bound (x : ℝ) :
    ∑' k : ℕ, |iteratedDeriv k expNegSq x| / (k.factorial : ℝ) *
      (1 / (8 * Real.exp 1)) ^ k ≤ 2 := by
  have hg : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k) :=
    summable_geometric_of_abs_lt_one (by norm_num)
  have hs : Summable (fun k : ℕ => |iteratedDeriv k expNegSq x| / (k.factorial : ℝ) *
      (1 / (8 * Real.exp 1)) ^ k) :=
    hg.of_nonneg_of_le (fun _ => by positivity) (gaussian_term_bound x)
  calc (∑' k : ℕ, |iteratedDeriv k expNegSq x| / (k.factorial : ℝ) *
          (1 / (8 * Real.exp 1)) ^ k)
      ≤ ∑' k : ℕ, (1 / 2 : ℝ) ^ k := hs.tsum_le_tsum (gaussian_term_bound x) hg
    _ = 2 := by
      rw [tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)]
      norm_num

end Qatlib.Papers.QSDPsolver17.MainResults.Gaussian
