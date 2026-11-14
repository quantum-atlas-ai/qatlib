/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

/-!
# Absolute error for a difference of probabilities

This module examines the error in a difference of two perturbed probabilities. It gives a
concrete failure of a proposed relative difference bound and proves the absolute bound `eps * (p
+ q)` from the individual relative error bounds. See [SchererEtAl2017] for the paper context.

## Main statements

* `relative_difference_counterexample`: Perturbing two copies of 1/2 to 101/200 and 99/200
  respects 1% individual relative error, but their difference violates the displayed relative
  error bound for the zero reference difference.
* `difference_absolute_bound`: Individual bounds `|p′ - p| ≤ eps * p` and `|q′ - q| ≤ eps * q`
  imply absolute difference error at most `eps * (p + q)`.

## References

* [Scherer et al., 2017][SchererEtAl2017]
-/

set_option autoImplicit false
namespace Qatlib.Papers.QLSAScatter15.ErrorScope

/-- Perturbing two copies of 1/2 to 101/200 and 99/200 respects 1% individual relative error,
but their difference violates the displayed relative error bound for the zero reference
difference. See [SchererEtAl2017]. -/
theorem relative_difference_counterexample :
    |(101/200:ℝ)-1/2| ≤ (1/100)*(1/2) ∧
    |(99/200:ℝ)-1/2| ≤ (1/100)*(1/2) ∧
    |((101/200:ℝ)-99/200)-((1/2:ℝ)-1/2)| >
      3*(1/100)*|(1/2:ℝ)-1/2| := by norm_num

/-- Individual bounds `|p′ - p| ≤ eps * p` and `|q′ - q| ≤ eps * q` imply absolute difference
error at most `eps * (p + q)`. See [SchererEtAl2017]. -/
theorem difference_absolute_bound (p q p' q' eps : ℝ)
    (hp : |p'-p| ≤ eps*p) (hq : |q'-q| ≤ eps*q) :
    |(p'-q')-(p-q)| ≤ eps*(p+q) := by
  rw [show (p'-q')-(p-q) = (p'-p)-(q'-q) by ring]
  calc
    |(p'-p)-(q'-q)| ≤ |p'-p|+|q'-q| := abs_sub _ _
    _ ≤ eps*p+eps*q := add_le_add hp hq
    _ = eps*(p+q) := by ring
end Qatlib.Papers.QLSAScatter15.ErrorScope
