/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSDPsolver17.MainResults.PaperInterface.PaperDefs
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Iterated Derivatives and Taylor Series Bounds for the Gaussian (Lemma 45)

This module formalizes Lemma 45 (Appendix, Equations (21)--(23), p. 30) of van
Apeldoorn, Gilyen, Gribling, and de Wolf establishing the three-term Hermite
derivative recurrence, pointwise growth bound, and scaled Taylor series bound
for `e^{-x^2}`.

## Main definitions

* `expNegSq`: The real Gaussian function `x |-> exp(-x^2)`.

## Main statements

* `lemma45_recurrence`: Lemma 45, Equation (21), recurrence for
  `iteratedDeriv (k + 1) expNegSq x`.
* `lemma45_deriv_bound`: Lemma 45, Equation (22),
  `|iteratedDeriv k expNegSq x| <= (2|x| + 2k)^k exp(-x^2)`.
* `lemma45_series_bound`: Lemma 45, Equation (23), geometric Taylor majorant
  with step `1 / (8 e)` bounded above by `2`.

## References

* [van Apeldoorn et al., 2020][VanApeldoornEtAl2020], Appendix, Lemma 45,
  Equations (21)--(23), p. 30.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QSDPsolver17.MainResults.HamiltonianSimulation
open Qatlib.Papers.QSDPsolver17.MainResults

/-- The Gaussian `e^{-x²}`. -/
def expNegSq : ℝ → ℝ := fun x => Real.exp (-(x ^ 2))

private def hermPoly : ℕ → Polynomial ℝ
  | 0 => 1
  | k + 1 => (hermPoly k).derivative - Polynomial.C 2 * Polynomial.X * hermPoly k

private theorem hermPoly_derivative (k : ℕ) :
    (hermPoly (k + 1)).derivative =
      -Polynomial.C (2 * ((k + 1 : ℕ) : ℝ)) * hermPoly k := by
  induction k with
  | zero => simp [hermPoly]
  | succ k ih =>
    rw [hermPoly, Polynomial.derivative_sub, ih]
    simp only [Polynomial.derivative_mul, Polynomial.derivative_neg,
      Polynomial.derivative_C, Polynomial.derivative_X, zero_mul, zero_add, mul_one, ih]
    rw [hermPoly]
    simp only [Nat.cast_add, Nat.cast_one, map_mul, map_add, map_ofNat, map_one]
    ring

private theorem iteratedDeriv_expNegSq_eq (k : ℕ) :
    iteratedDeriv k expNegSq = fun x => (hermPoly k).eval x * expNegSq x := by
  induction k with
  | zero => simp [iteratedDeriv_zero, hermPoly]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have hf : HasDerivAt expNegSq (Real.exp (-(x ^ 2)) * -(2 * x)) x := by
      unfold expNegSq
      convert (hasDerivAt_pow 2 x).neg.exp using 1
      norm_num
    calc
      _ = (hermPoly k).derivative.eval x * expNegSq x +
          (hermPoly k).eval x * (Real.exp (-(x ^ 2)) * -(2 * x)) :=
        ((hermPoly k).hasDerivAt x |>.mul hf).deriv
      _ = _ := by
        simp only [hermPoly, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_X, expNegSq]
        ring

/-- **Lemma 45, recurrence (21)** (arXiv:1705.01843v4, p. 30).  For all
`k ∈ ℕ`,
`∂_x^{k+1} e^{-x²} = -2x ∂_x^k e^{-x²} - 2k ∂_x^{k-1} e^{-x²}`. -/
theorem lemma45_recurrence (k : ℕ) (x : ℝ) :
    iteratedDeriv (k + 1) expNegSq x =
      -2 * x * iteratedDeriv k expNegSq x -
        2 * (k : ℝ) * iteratedDeriv (k - 1) expNegSq x := by
  simp only [iteratedDeriv_expNegSq_eq]
  cases k with
  | zero => simp [hermPoly]
  | succ k =>
    rw [hermPoly, hermPoly_derivative]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_neg,
      Polynomial.eval_C, Polynomial.eval_X, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    ring

/-- **Lemma 45, bound (22)** (arXiv:1705.01843v4, p. 30).  For all `x ∈ ℝ`,
`|∂_x^k e^{-x²}| ≤ (2|x| + 2k)^k e^{-x²}`. -/
theorem lemma45_deriv_bound (k : ℕ) (x : ℝ) :
    |iteratedDeriv k expNegSq x| ≤
      (2 * |x| + 2 * (k : ℝ)) ^ k * Real.exp (-(x ^ 2)) := by
  induction k using Nat.twoStepInduction with
  | zero => simp [iteratedDeriv_zero, expNegSq]
  | one =>
    have h := lemma45_recurrence 0 x
    simp only [zero_add, Nat.cast_zero, mul_zero, zero_mul, sub_zero,
      iteratedDeriv_zero] at h
    rw [h]
    simp only [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      expNegSq, abs_of_pos (Real.exp_pos _),
      Nat.cast_one, mul_one, pow_one]
    nlinarith [Real.exp_pos (-(x ^ 2))]
  | more k ih₀ ih₁ =>
    let b : ℝ := 2 * |x| + 2 * ((k + 2 : ℕ) : ℝ)
    have hb : 1 ≤ b := by
      dsimp [b]
      push_cast
      nlinarith [abs_nonneg x, Nat.cast_nonneg (α := ℝ) k]
    have h₀ : (2 * |x| + 2 * (k : ℝ)) ^ k ≤ b ^ (k + 1) := by
      calc
        _ ≤ b ^ k := by
          apply pow_le_pow_left₀ (by positivity)
          dsimp [b]
          push_cast
          linarith
        _ ≤ b ^ (k + 1) := pow_le_pow_right₀ hb (Nat.le_succ k)
    have h₁ : (2 * |x| + 2 * ((k + 1 : ℕ) : ℝ)) ^ (k + 1) ≤ b ^ (k + 1) := by
      apply pow_le_pow_left₀ (by positivity)
      dsimp [b]
      push_cast
      linarith
    have hc : 2 * |x| + 2 * ((k + 1 : ℕ) : ℝ) ≤ b := by
      dsimp [b]
      push_cast
      linarith
    calc
      |iteratedDeriv (k + 2) expNegSq x| ≤
          2 * |x| * |iteratedDeriv (k + 1) expNegSq x| +
            2 * ((k + 1 : ℕ) : ℝ) * |iteratedDeriv k expNegSq x| := by
        rw [show k + 2 = (k + 1) + 1 by omega, lemma45_recurrence]
        simpa only [Nat.add_sub_cancel, abs_mul, abs_neg,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (k + 1))] using
          abs_sub (-2 * x * iteratedDeriv (k + 1) expNegSq x)
            (2 * ((k + 1 : ℕ) : ℝ) * iteratedDeriv k expNegSq x)
      _ ≤ 2 * |x| * (b ^ (k + 1) * Real.exp (-(x ^ 2))) +
          2 * ((k + 1 : ℕ) : ℝ) * (b ^ (k + 1) * Real.exp (-(x ^ 2))) := by
        gcongr
        · exact ih₁.trans (mul_le_mul_of_nonneg_right h₁ (Real.exp_nonneg _))
        · exact ih₀.trans (mul_le_mul_of_nonneg_right h₀ (Real.exp_nonneg _))
      _ = (2 * |x| + 2 * ((k + 1 : ℕ) : ℝ)) *
          b ^ (k + 1) * Real.exp (-(x ^ 2)) := by ring
      _ ≤ b * b ^ (k + 1) * Real.exp (-(x ^ 2)) := by gcongr
      _ = (2 * |x| + 2 * ((k + 2 : ℕ) : ℝ)) ^ (k + 2) *
          Real.exp (-(x ^ 2)) := by
        change b * b ^ (k + 1) * _ = b ^ ((k + 1) + 1) * _
        rw [pow_succ' b (k + 1)]

private theorem scaled_power_bound (k : ℕ) (hk : k ≠ 0) (x : ℝ) :
    (2 * |x| + 2 * (k : ℝ)) ^ k / (k.factorial : ℝ) ≤
      (2 * Real.exp 1) ^ k * Real.exp |x| := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hexp : (1 + |x| / (k : ℝ)) ^ k ≤ Real.exp |x| := by
    calc
      _ ≤ (Real.exp (|x| / (k : ℝ))) ^ k := by
        apply pow_le_pow_left₀ (by positivity)
        linarith [Real.add_one_le_exp (|x| / (k : ℝ))]
      _ = Real.exp |x| := by
        rw [← Real.exp_nat_mul]
        congr 1
        field_simp
  have hfact : (k : ℝ) ^ k / (k.factorial : ℝ) ≤ (Real.exp 1) ^ k := by
    simpa only [← Real.exp_nat_mul, mul_one] using
      Real.pow_div_factorial_le_exp (k : ℝ) (Nat.cast_nonneg k) k
  calc
    _ = (2 : ℝ) ^ k * ((k : ℝ) ^ k / (k.factorial : ℝ)) *
        (1 + |x| / (k : ℝ)) ^ k := by
      rw [show 2 * |x| + 2 * (k : ℝ) =
        2 * (k : ℝ) * (1 + |x| / (k : ℝ)) by field_simp; ring]
      rw [mul_pow, mul_pow]
      ring
    _ ≤ (2 : ℝ) ^ k * (Real.exp 1) ^ k * Real.exp |x| := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hfact (by positivity)) hexp
        (by positivity) (by positivity)
    _ = _ := by rw [mul_pow]

private theorem exp_abs_sub_sq_le (x : ℝ) : Real.exp (|x| - x ^ 2) ≤ 3 := by
  have hsq : |x| - x ^ 2 ≤ (1 / 4 : ℝ) := by
    nlinarith [sq_nonneg (|x| - 1 / 2), sq_abs x]
  have hlow : (3 / 4 : ℝ) ≤ Real.exp (-1 / 4) := by
    linarith [Real.add_one_le_exp (-1 / 4 : ℝ)]
  have hmul := mul_le_mul_of_nonneg_right hlow (Real.exp_nonneg (1 / 4))
  rw [← Real.exp_add] at hmul
  norm_num at hmul
  exact (Real.exp_le_exp.mpr hsq).trans (by linarith)

/-- **Lemma 45, sum bound (23)** (arXiv:1705.01843v4, p. 30).  For all
`x ∈ ℝ`,
`Σ_{k≥0} |∂_x^k e^{-x²}|/k! · (1/(8e))^k ≤ 2`. -/
theorem lemma45_series_bound (x : ℝ) :
    ∑' k : ℕ, |iteratedDeriv k expNegSq x| / (k.factorial : ℝ) *
        (1 / (8 * Real.exp 1)) ^ k ≤ 2 := by
  let term (k : ℕ) : ℝ := |iteratedDeriv k expNegSq x| / (k.factorial : ℝ) *
    (1 / (8 * Real.exp 1)) ^ k
  let g (k : ℕ) : ℝ := if k = 0 then 1 else 3 * (1 / 4 : ℝ) ^ k
  have hterm : ∀ k, term k ≤ g k := by
    intro k
    cases k with
    | zero =>
      simpa [term, g, iteratedDeriv_zero, expNegSq, Real.exp_pos] using
        (Real.exp_le_exp.mpr (neg_nonpos.mpr (sq_nonneg x)))
    | succ k =>
      have hk : k + 1 ≠ 0 := Nat.succ_ne_zero k
      have hstep : (2 * Real.exp 1) * (1 / (8 * Real.exp 1)) = (1 / 4 : ℝ) := by
        field_simp
        norm_num
      calc
        term (k + 1) ≤
            ((2 * |x| + 2 * ((k + 1 : ℕ) : ℝ)) ^ (k + 1) /
              ((k + 1).factorial : ℝ)) * Real.exp (-(x ^ 2)) *
                (1 / (8 * Real.exp 1)) ^ (k + 1) := by
          dsimp [term]
          have h := lemma45_deriv_bound (k + 1) x
          calc
            _ ≤ ((2 * |x| + 2 * ((k + 1 : ℕ) : ℝ)) ^ (k + 1) *
                Real.exp (-(x ^ 2))) / ((k + 1).factorial : ℝ) *
                  (1 / (8 * Real.exp 1)) ^ (k + 1) := by gcongr
            _ = _ := by ring
        _ ≤ ((2 * Real.exp 1) ^ (k + 1) * Real.exp |x|) *
            Real.exp (-(x ^ 2)) * (1 / (8 * Real.exp 1)) ^ (k + 1) := by
          gcongr
          exact scaled_power_bound (k + 1) hk x
        _ = Real.exp (|x| - x ^ 2) * (1 / 4 : ℝ) ^ (k + 1) := by
          rw [sub_eq_add_neg, Real.exp_add, ← hstep,
            mul_pow (2 * Real.exp 1) (1 / (8 * Real.exp 1))]
          ring
        _ ≤ 3 * (1 / 4 : ℝ) ^ (k + 1) := by
          exact mul_le_mul_of_nonneg_right (exp_abs_sub_sq_le x) (by positivity)
        _ = g (k + 1) := by simp [g]
  have hg_tail : Summable (fun k : ℕ => g (k + 1)) := by
    simpa [g, pow_succ, mul_assoc] using
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
        (by norm_num : (1 / 4 : ℝ) < 1)).mul_left (3 * (1 / 4 : ℝ))
  have hg : Summable g := (summable_nat_add_iff 1).mp hg_tail
  have ht : Summable term := hg.of_nonneg_of_le (fun k => by dsimp [term]; positivity) hterm
  calc
    (∑' k : ℕ, term k) ≤ ∑' k : ℕ, g k := ht.tsum_le_tsum hterm hg
    _ = 2 := by
      rw [hg.tsum_eq_zero_add]
      simp only [g, Nat.succ_ne_zero, ite_true, ite_false]
      simp_rw [pow_succ, ← mul_assoc]
      rw [tsum_mul_right, tsum_mul_left,
        tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
          (by norm_num : (1 / 4 : ℝ) < 1)]
      norm_num

end Qatlib.Papers.QSDPsolver17.MainResults.HamiltonianSimulation
