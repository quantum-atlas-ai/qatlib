/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

@[expose] public section


/-! # Gaussian derivative recurrence, arXiv:1705.01843v4 Lemma 45, pp. 56–57.
The proof differentiates actual smooth functions at every order; no polynomial
factor, derivative bound, or recurrence is assumed.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QSDPsolver17.MainResults.Gaussian

/-- The real Gaussian used in the smooth Hamiltonian function implementation. -/
def expNegSq (x : ℝ) : ℝ := Real.exp (-(x ^ 2))

/-- The Gaussian is smooth to every finite order. -/
theorem gaussian_smooth (n : ℕ) : ContDiff ℝ n expNegSq := by
  unfold expNegSq
  fun_prop

/-- Each iterated derivative has the next iterated derivative as its actual derivative. -/
theorem hasDerivAt_iter (n : ℕ) (x : ℝ) :
    HasDerivAt (iteratedDeriv n expNegSq) (iteratedDeriv (n + 1) expNegSq x) x := by
  rw [iteratedDeriv_succ]
  exact ((gaussian_smooth (n + 1)).differentiable_iteratedDeriv' n x).hasDerivAt

/-- The first derivative of the Gaussian is minus twice its argument times the Gaussian. -/
theorem gaussian_first (x : ℝ) :
    deriv expNegSq x = -2 * x * expNegSq x := by
  have h := (((hasDerivAt_id x).pow 2).neg.exp).deriv
  change deriv expNegSq x = Real.exp (-(x ^ 2)) * -((2 : ℝ) * x ^ (2 - 1) * 1) at h
  calc deriv expNegSq x = Real.exp (-(x ^ 2)) * -((2 : ℝ) * x ^ (2 - 1) * 1) := h
    _ = -2 * x * expNegSq x := by unfold expNegSq; ring

set_option backward.isDefEq.respectTransparency false in
/-- The second derivative is the quadratic factor times the Gaussian. -/
theorem gaussian_second (x : ℝ) :
    iteratedDeriv 2 expNegSq x = (4 * x ^ 2 - 2) * expNegSq x := by
  have hfirst : deriv expNegSq = fun y => -2 * y * expNegSq y := funext gaussian_first
  have hd0 := ((hasDerivAt_id x).const_mul (-2)).fun_mul (hasDerivAt_iter 0 x)
  have hd : HasDerivAt (fun y => -2 * y * expNegSq y)
      (-2 * expNegSq x + (-2 * x) * deriv expNegSq x) x := by
    simpa only [Pi.mul_apply, id_eq, mul_one, Nat.zero_add,
      iteratedDeriv_zero, iteratedDeriv_one] using hd0
  calc iteratedDeriv 2 expNegSq x = deriv (deriv expNegSq) x := by
        rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]
    _ = deriv (fun y => -2 * y * expNegSq y) x :=
      congrArg (fun g : ℝ → ℝ => deriv g x) hfirst
    _ = -2 * expNegSq x + (-2 * x) * deriv expNegSq x := hd.deriv
    _ = (4 * x ^ 2 - 2) * expNegSq x := by rw [gaussian_first]; ring

set_option backward.isDefEq.respectTransparency false in
/-- Consecutive Gaussian derivatives satisfy the two-step recurrence, starting at order two. -/
theorem recurrence_shift (n : ℕ) (x : ℝ) :
    iteratedDeriv (n + 2) expNegSq x =
      -2 * x * iteratedDeriv (n + 1) expNegSq x -
        2 * ((n + 1 : ℕ) : ℝ) * iteratedDeriv n expNegSq x := by
  induction n generalizing x with
  | zero =>
      simp only [Nat.zero_add, Nat.cast_one, iteratedDeriv_zero, iteratedDeriv_one]
      rw [gaussian_second, gaussian_first]
      ring
  | succ n ih =>
      have hf : iteratedDeriv (n + 2) expNegSq = fun y =>
          -2 * y * iteratedDeriv (n + 1) expNegSq y -
            2 * ((n + 1 : ℕ) : ℝ) * iteratedDeriv n expNegSq y := funext ih
      have hd0 := (((hasDerivAt_id x).const_mul (-2)).fun_mul
        (hasDerivAt_iter (n + 1) x)).fun_sub
          ((hasDerivAt_iter n x).const_mul (2 * ((n + 1 : ℕ) : ℝ)))
      have hd : HasDerivAt
          (fun y => -2 * y * iteratedDeriv (n + 1) expNegSq y -
            2 * ((n + 1 : ℕ) : ℝ) * iteratedDeriv n expNegSq y)
          (-2 * iteratedDeriv (n + 1) expNegSq x +
            (-2 * x) * iteratedDeriv (n + 1 + 1) expNegSq x -
            2 * ((n + 1 : ℕ) : ℝ) * iteratedDeriv (n + 1) expNegSq x) x := by
        simpa only [Pi.mul_apply, Pi.sub_apply, id_eq, mul_one] using hd0
      have hdeq : iteratedDeriv (n + 1 + 2) expNegSq x =
          (-2 * iteratedDeriv (n + 1) expNegSq x +
              (-2 * x) * iteratedDeriv (n + 1 + 1) expNegSq x) -
            (2 * ((n + 1 : ℕ) : ℝ)) * iteratedDeriv (n + 1) expNegSq x := by
        calc iteratedDeriv (n + 1 + 2) expNegSq x
              = deriv (iteratedDeriv (n + 2) expNegSq) x := by
                rw [show n + 1 + 2 = (n + 2) + 1 by omega, iteratedDeriv_succ]
          _ = deriv (fun y => -2 * y * iteratedDeriv (n + 1) expNegSq y -
                2 * ((n + 1 : ℕ) : ℝ) * iteratedDeriv n expNegSq y) x :=
              congrArg (fun g : ℝ → ℝ => deriv g x) hf
          _ = _ := hd.deriv
      rw [hdeq]
      push_cast
      ring

/-- Lemma 45, Eq. (21): the recurrence also holds at order zero with the zero coefficient. -/
theorem lemma45_recurrence (k : ℕ) (x : ℝ) :
    iteratedDeriv (k + 1) expNegSq x =
      -2 * x * iteratedDeriv k expNegSq x -
        2 * (k : ℝ) * iteratedDeriv (k - 1) expNegSq x := by
  cases k with
  | zero => simp [gaussian_first]
  | succ n => simpa [Nat.succ_eq_add_one] using recurrence_shift n x

/-- Lemma 45, Eq. (22): all Gaussian derivatives satisfy the polynomial-envelope bound. -/
theorem lemma45_deriv_bound (k : ℕ) (x : ℝ) :
    |iteratedDeriv k expNegSq x| ≤
      (2 * |x| + 2 * (k : ℝ)) ^ k * Real.exp (-(x ^ 2)) := by
  change |iteratedDeriv k expNegSq x| ≤ (2 * |x| + 2 * (k : ℝ)) ^ k * expNegSq x
  have he : 0 < expNegSq x := Real.exp_pos _
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simp [iteratedDeriv_zero, abs_of_pos he]
    | succ k =>
      cases k with
      | zero =>
        simp only [Nat.zero_add, Nat.cast_one, pow_one, iteratedDeriv_one, gaussian_first]
        have hcoef : 2 * |x| ≤ 2 * |x| + 2 := by linarith
        simpa only [abs_mul, show |(-2 : ℝ)| = 2 by norm_num, abs_of_pos he, mul_one] using
          mul_le_mul_of_nonneg_right hcoef he.le
      | succ n =>
        change |iteratedDeriv (n + 2) expNegSq x| ≤
          (2 * |x| + 2 * ((n + 2 : ℕ) : ℝ)) ^ (n + 2) * expNegSq x
        let B : ℝ := 2 * |x| + 2 * ((n + 2 : ℕ) : ℝ)
        have hB : 0 ≤ B := by dsimp [B]; positivity
        have hbase1 : 2 * |x| + 2 * ((n + 1 : ℕ) : ℝ) ≤ B := by
          dsimp [B]
          push_cast
          linarith
        have hbase0 : 2 * |x| + 2 * (n : ℝ) ≤ B := by
          dsimp [B]
          push_cast
          linarith
        have hpow1 : (2 * |x| + 2 * ((n + 1 : ℕ) : ℝ)) ^ (n + 1) ≤ B ^ (n + 1) :=
          pow_le_pow_left₀ (by positivity) hbase1 _
        have hpow0 : (2 * |x| + 2 * (n : ℝ)) ^ n ≤ B ^ n :=
          pow_le_pow_left₀ (by positivity) hbase0 _
        have hprev : |iteratedDeriv (n + 1) expNegSq x| ≤ B ^ (n + 1) * expNegSq x :=
          (ih (n + 1) (by omega)).trans (mul_le_mul_of_nonneg_right hpow1 he.le)
        have hprev0 : |iteratedDeriv n expNegSq x| ≤ B ^ n * expNegSq x :=
          (ih n (by omega)).trans (mul_le_mul_of_nonneg_right hpow0 he.le)
        have hsmall : 2 * ((n + 1 : ℕ) : ℝ) ≤ B := by
          dsimp [B]
          push_cast
          linarith [abs_nonneg x]
        have hfactor : 2 * |x| + 1 ≤ B := by
          dsimp [B]
          push_cast
          linarith [Nat.cast_nonneg (α := ℝ) n]
        have hpoly : 2 * |x| * B + 2 * ((n + 1 : ℕ) : ℝ) ≤ B ^ 2 := by
          calc 2 * |x| * B + 2 * ((n + 1 : ℕ) : ℝ)
              ≤ 2 * |x| * B + B := by linarith [hsmall]
            _ = (2 * |x| + 1) * B := by ring
            _ ≤ B * B := mul_le_mul_of_nonneg_right hfactor hB
            _ = B ^ 2 := by ring
        have hrec : iteratedDeriv (n + 2) expNegSq x =
            -2 * x * iteratedDeriv (n + 1) expNegSq x -
              2 * ((n + 1 : ℕ) : ℝ) * iteratedDeriv n expNegSq x :=
          recurrence_shift n x
        calc |iteratedDeriv (n + 2) expNegSq x|
            = |-2 * x * iteratedDeriv (n + 1) expNegSq x -
                2 * ((n + 1 : ℕ) : ℝ) * iteratedDeriv n expNegSq x| := congrArg abs hrec
          _ ≤ |-2 * x * iteratedDeriv (n + 1) expNegSq x| +
                |2 * ((n + 1 : ℕ) : ℝ) * iteratedDeriv n expNegSq x| := by
              simpa only [sub_eq_add_neg, abs_neg] using
                abs_add_le (-2 * x * iteratedDeriv (n + 1) expNegSq x)
                  (-(2 * ((n + 1 : ℕ) : ℝ) * iteratedDeriv n expNegSq x))
          _ = 2 * |x| * |iteratedDeriv (n + 1) expNegSq x| +
                2 * ((n + 1 : ℕ) : ℝ) * |iteratedDeriv n expNegSq x| := by
              have hn1 : 0 ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
              simp only [abs_mul, show |(-2 : ℝ)| = 2 by norm_num,
                show |(2 : ℝ)| = 2 by norm_num, abs_of_nonneg hn1]
          _ ≤ 2 * |x| * (B ^ (n + 1) * expNegSq x) +
                2 * ((n + 1 : ℕ) : ℝ) * (B ^ n * expNegSq x) := by
              exact add_le_add (mul_le_mul_of_nonneg_left hprev (by positivity))
                (mul_le_mul_of_nonneg_left hprev0 (by positivity))
          _ = (2 * |x| * B + 2 * ((n + 1 : ℕ) : ℝ)) * B ^ n * expNegSq x := by
              rw [pow_succ]
              ring
          _ ≤ B ^ 2 * B ^ n * expNegSq x := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hpoly (pow_nonneg hB _)) he.le
          _ = B ^ (n + 2) * expNegSq x := by rw [pow_add]; ring


end Qatlib.Papers.QSDPsolver17.MainResults.Gaussian
