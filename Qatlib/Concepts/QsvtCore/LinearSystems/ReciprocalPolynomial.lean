/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Complex.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.Ring

/-!
# Geometric reciprocal polynomials

`reciprocalFactor` is a finite geometric sum, and `reciprocalPolynomial` is the odd polynomial
obtained by composing this sum with `X ^ 2` and multiplying by `X`. The identity
`X_mul_reciprocalPolynomial` gives an exact residual formula for reciprocal approximation in
quantum singular value transformation [GilyenSuLowWiebe2019].

The module proves evaluation, parity, and degree formulas over the reals and transfers them to
`complexReciprocalPolynomial`.

## Main statements

* `X_mul_reciprocalPolynomial`: identifies the polynomial residual as a power of `1 - X ^ 2`.
* `inv_sub_reciprocalPolynomial_eval`: expresses the reciprocal approximation error at a nonzero
  real input.
* `reciprocalPolynomial_natDegree`: computes the degree for a positive truncation index.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

namespace Qatlib.Concepts.QsvtCore.LinearSystems

open Polynomial
open scoped BigOperators

/-- The geometric polynomial ∑ k < n, (1 - X)^k over the reals. -/
noncomputable def reciprocalFactor (n : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range n, (1 - X) ^ k

/-- The odd reciprocal approximant X ∑ k < n, (1 - X²)^k over the reals. -/
noncomputable def reciprocalPolynomial (n : ℕ) : Polynomial ℝ :=
  X * (reciprocalFactor n).comp (X ^ 2)

/-- The polynomial `reciprocalPolynomial n` with its real coefficients mapped to the complex
numbers. -/
noncomputable def complexReciprocalPolynomial (n : ℕ) : Polynomial ℂ :=
  (reciprocalPolynomial n).map Complex.ofRealHom

/-- The geometric reciprocal factor with no terms is zero. -/
@[simp] theorem reciprocalFactor_zero : reciprocalFactor 0 = 0 := by
  simp [reciprocalFactor]

/-- The geometric reciprocal factor with one term is the constant polynomial one. -/
@[simp] theorem reciprocalFactor_one : reciprocalFactor 1 = 1 := by
  simp [reciprocalFactor]

/-- The reciprocal approximant with truncation index zero is zero. -/
@[simp] theorem reciprocalPolynomial_zero : reciprocalPolynomial 0 = 0 := by
  simp [reciprocalPolynomial]

/-- The reciprocal approximant with truncation index one is `X`. -/
@[simp] theorem reciprocalPolynomial_one : reciprocalPolynomial 1 = X := by
  simp [reciprocalPolynomial]

/-- Expands the reciprocal polynomial as X times the finite geometric sum in 1 - X². -/
theorem reciprocalPolynomial_eq_sum (n : ℕ) :
    reciprocalPolynomial n =
      X * ∑ k ∈ Finset.range n, (1 - X ^ 2 : Polynomial ℝ) ^ k := by
  simp [reciprocalPolynomial, reciprocalFactor]

/-- Multiplication by `X` turns the reciprocal factor into the geometric residual 1 - (1 - X)^n. -/
theorem X_mul_reciprocalFactor (n : ℕ) :
    X * reciprocalFactor n = 1 - (1 - X : Polynomial ℝ) ^ n := by
  unfold reciprocalFactor
  convert mul_neg_geom_sum (1 - (X : Polynomial ℝ)) n using 1
  ring

/-- Multiplication by `X` turns the reciprocal approximant into 1 - (1 - X²)^n. -/
theorem X_mul_reciprocalPolynomial (n : ℕ) :
    X * reciprocalPolynomial n = 1 - (1 - X ^ 2 : Polynomial ℝ) ^ n := by
  rw [reciprocalPolynomial_eq_sum]
  convert mul_neg_geom_sum (1 - (X : Polynomial ℝ) ^ 2) n using 1
  ring

/-- Evaluates the reciprocal polynomial as x times the finite geometric sum in 1 - x². -/
theorem reciprocalPolynomial_eval_sum (n : ℕ) (x : ℝ) :
    (reciprocalPolynomial n).eval x =
      x * ∑ k ∈ Finset.range n, (1 - x ^ 2) ^ k := by
  simp [reciprocalPolynomial_eq_sum, Polynomial.eval_finsetSum]

/-- The product of x and the reciprocal polynomial evaluated at x equals 1 - (1 - x²)^n. -/
theorem mul_reciprocalPolynomial_eval (n : ℕ) (x : ℝ) :
    x * (reciprocalPolynomial n).eval x = 1 - (1 - x ^ 2) ^ n := by
  have h := congrArg (fun p : Polynomial ℝ => p.eval x) (X_mul_reciprocalPolynomial n)
  simpa using h

/-- At a nonzero real input x, the reciprocal polynomial evaluates to (1 - (1 - x²)^n) / x. -/
theorem reciprocalPolynomial_eval_div (n : ℕ) {x : ℝ} (hx : x ≠ 0) :
    (reciprocalPolynomial n).eval x = (1 - (1 - x ^ 2) ^ n) / x := by
  apply (eq_div_iff hx).2
  simpa only [mul_comm] using mul_reciprocalPolynomial_eval n x

/-- At a nonzero real input x, the error from x⁻¹ is exactly (1 - x²)^n / x. -/
theorem inv_sub_reciprocalPolynomial_eval (n : ℕ) {x : ℝ} (hx : x ≠ 0) :
    x⁻¹ - (reciprocalPolynomial n).eval x = (1 - x ^ 2) ^ n / x := by
  rw [reciprocalPolynomial_eval_div n hx]
  field_simp
  ring

/-- Every reciprocal polynomial vanishes at zero. -/
@[simp] theorem reciprocalPolynomial_eval_zero (n : ℕ) :
    (reciprocalPolynomial n).eval 0 = 0 := by
  simp [reciprocalPolynomial]

/-- A reciprocal polynomial with positive truncation index takes the value one at one. -/
theorem reciprocalPolynomial_eval_one {n : ℕ} (hn : 0 < n) :
    (reciprocalPolynomial n).eval 1 = 1 := by
  simpa [zero_pow (Nat.ne_of_gt hn)] using mul_reciprocalPolynomial_eval n 1

/-- The reciprocal polynomial is nonzero when its truncation index is positive. -/
theorem reciprocalPolynomial_ne_zero {n : ℕ} (hn : 0 < n) :
    reciprocalPolynomial n ≠ 0 := by
  intro h
  have he := reciprocalPolynomial_eval_one hn
  simp [h] at he

/-- Composition with `-X` negates the reciprocal polynomial. -/
theorem reciprocalPolynomial_comp_neg_X (n : ℕ) :
    (reciprocalPolynomial n).comp (-X) = -reciprocalPolynomial n := by
  simp [reciprocalPolynomial, Polynomial.comp_assoc]

/-- The reciprocal polynomial is odd as a real-valued function. -/
theorem reciprocalPolynomial_eval_neg (n : ℕ) (x : ℝ) :
    (reciprocalPolynomial n).eval (-x) = -(reciprocalPolynomial n).eval x := by
  have h := congrArg (fun p : Polynomial ℝ => p.eval x)
    (reciprocalPolynomial_comp_neg_X n)
  simpa using h

/-- For positive n, the reciprocal polynomial has natural degree 2n - 1. -/
theorem reciprocalPolynomial_natDegree {n : ℕ} (hn : 0 < n) :
    (reciprocalPolynomial n).natDegree = 2 * n - 1 := by
  have hd : (1 - X ^ 2 : Polynomial ℝ).natDegree = 2 := by
    rw [Polynomial.natDegree_sub_eq_right_of_natDegree_lt (by simp)]
    simp
  have hp : ((1 - X ^ 2 : Polynomial ℝ) ^ n).natDegree = 2 * n := by
    simp [hd, Nat.mul_comm]
  have hr : (1 - (1 - X ^ 2 : Polynomial ℝ) ^ n).natDegree = 2 * n := by
    rw [Polynomial.natDegree_sub_eq_right_of_natDegree_lt]
    · exact hp
    · simp only [Polynomial.natDegree_one, hp]
      omega
  have hm := congrArg Polynomial.natDegree (X_mul_reciprocalPolynomial n)
  rw [Polynomial.natDegree_mul Polynomial.X_ne_zero (reciprocalPolynomial_ne_zero hn),
    Polynomial.natDegree_X, hr] at hm
  omega

/-- The natural degree of the reciprocal polynomial is at most 2n - 1 for every truncation
index. -/
theorem reciprocalPolynomial_natDegree_le (n : ℕ) :
    (reciprocalPolynomial n).natDegree ≤ 2 * n - 1 := by
  cases n with
  | zero => simp
  | succ n => exact (reciprocalPolynomial_natDegree (Nat.succ_pos n)).le

/-- Expresses the complex reciprocal polynomial as `X` times the complexified reciprocal factor
composed with `X ^ 2`. -/
theorem complexReciprocalPolynomial_eq_factor (n : ℕ) :
    complexReciprocalPolynomial n =
      X * ((reciprocalFactor n).map Complex.ofRealHom).comp (X ^ 2) := by
  simp [complexReciprocalPolynomial, reciprocalPolynomial, Polynomial.map_comp]

/-- Evaluating the complex reciprocal polynomial at a real input gives the complex embedding of
the real polynomial's value. -/
theorem complexReciprocalPolynomial_eval_real (n : ℕ) (x : ℝ) :
    (complexReciprocalPolynomial n).eval (x : ℂ) =
      (((reciprocalPolynomial n).eval x : ℝ) : ℂ) := by
  exact Polynomial.eval_map_apply (f := Complex.ofRealHom) x

/-- For positive n, the complex reciprocal polynomial has natural degree 2n - 1. -/
theorem complexReciprocalPolynomial_natDegree {n : ℕ} (hn : 0 < n) :
    (complexReciprocalPolynomial n).natDegree = 2 * n - 1 := by
  rw [complexReciprocalPolynomial,
    Polynomial.natDegree_map_eq_of_injective Complex.ofReal_injective]
  exact reciprocalPolynomial_natDegree hn

/-- The complex reciprocal polynomial is odd on complex inputs. -/
theorem complexReciprocalPolynomial_eval_neg (n : ℕ) (z : ℂ) :
    (complexReciprocalPolynomial n).eval (-z) =
      -(complexReciprocalPolynomial n).eval z := by
  simp [complexReciprocalPolynomial_eq_factor]

/-- The reciprocal polynomial with truncation index two takes the value 69/64 at 3/4. -/
theorem reciprocalPolynomial_two_at_three_quarters :
    (reciprocalPolynomial 2).eval (3 / 4 : ℝ) = 69 / 64 := by
  norm_num [reciprocalPolynomial_eval_sum, Finset.sum_range_succ]

end Qatlib.Concepts.QsvtCore.LinearSystems
