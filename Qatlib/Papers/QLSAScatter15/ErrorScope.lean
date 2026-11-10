/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

set_option autoImplicit false
namespace Qatlib.Papers.QLSAScatter15.ErrorScope

theorem relative_difference_counterexample :
    |(101/200:ℝ)-1/2| ≤ (1/100)*(1/2) ∧
    |(99/200:ℝ)-1/2| ≤ (1/100)*(1/2) ∧
    |((101/200:ℝ)-99/200)-((1/2:ℝ)-1/2)| >
      3*(1/100)*|(1/2:ℝ)-1/2| := by norm_num

theorem difference_absolute_bound (p q p' q' eps : ℝ)
    (hp : |p'-p| ≤ eps*p) (hq : |q'-q| ≤ eps*q) :
    |(p'-q')-(p-q)| ≤ eps*(p+q) := by
  rw [show (p'-q')-(p-q) = (p'-p)-(q'-q) by ring]
  calc
    |(p'-p)-(q'-q)| ≤ |p'-p|+|q'-q| := abs_sub _ _
    _ ≤ eps*p+eps*q := add_le_add hp hq
    _ = eps*(p+q) := by ring
end Qatlib.Papers.QLSAScatter15.ErrorScope
