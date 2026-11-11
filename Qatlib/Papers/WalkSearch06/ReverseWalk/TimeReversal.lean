/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Order.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Time reversal and walk discriminants

This module defines the time reversal of a real transition matrix relative to a weight vector
and proves its basic algebraic and stochastic identities. It defines the forward/reverse
discriminant, identifies its diagonal similarity formula for positive weights, and proves
symmetry under detailed balance.

For quantum-walk search background, see [MagniezNayakRolandSantha2011].

## Main statements

* `timeReversal_involutive`: reversing twice recovers the original matrix for positive weights.
* `timeReversal_row_sum`: stationary positive weights give unit reversed row sums.
* `discriminant_eq_similarity`: entrywise diagonal similarity formula.

## References

* [Magniez et al., 2011][MagniezNayakRolandSantha2011]
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Qatlib.Papers.WalkSearch06.ReverseWalk.TimeReversal

open scoped BigOperators

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The time-reversed matrix with entries `π y * P y x / π x`, using real division for all
weight vectors. See [Definition 1 (Quantum walk)][MagniezNayakRolandSantha2011]. -/
noncomputable def timeReversal (P : Matrix X X ℝ) (π : X → ℝ) : Matrix X X ℝ :=
  fun x y => π y * P y x / π x

omit [Fintype X] [DecidableEq X] in

/-- The entry of the time-reversed matrix at `(x, y)` is `π y * P y x / π x`. -/
theorem timeReversal_apply (P : Matrix X X ℝ) (π : X → ℝ) (x y : X) :
    timeReversal P π x y = π y * P y x / π x := rfl

/-- With positive weights, detailed balance makes the time-reversed matrix equal to the original
matrix. See [Definition 1 (Quantum walk)][MagniezNayakRolandSantha2011]. -/
theorem timeReversal_eq_of_detailedBalance (P : Matrix X X ℝ) (π : X → ℝ)
    (hπ : ∀ x, 0 < π x)
    (hdb : ∀ x y, π x * P x y = π y * P y x) :
    timeReversal P π = P := by
  funext x y
  rw [timeReversal_apply, div_eq_iff (hπ x).ne']
  rw [mul_comm (P x y) (π x)]
  exact (hdb x y).symm

/-- Nonnegative transition entries and positive weights give nonnegative time-reversed entries. -/
theorem timeReversal_nonneg (P : Matrix X X ℝ) (π : X → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (hπ : ∀ x, 0 < π x) :
    ∀ x y, 0 ≤ timeReversal P π x y := by
  intro x y
  rw [timeReversal_apply]
  exact div_nonneg (mul_nonneg (hπ y).le (hP y x)) (hπ x).le

/-- For positive stationary weights, every row of the time-reversed matrix sums to one. -/
theorem timeReversal_row_sum (P : Matrix X X ℝ) (π : X → ℝ)
    (hπ : ∀ x, 0 < π x) (hstat : ∀ y, ∑ x, π x * P x y = π y) :
    ∀ x, ∑ y, timeReversal P π x y = 1 := by
  intro x
  have hx : π x ≠ 0 := (hπ x).ne'
  have hsum : ∑ y, timeReversal P π x y = (∑ y, π y * P y x) / π x := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl ?_
    intro y _
    rw [timeReversal_apply]
  rw [hsum, hstat x]
  exact div_self hx

/-- For positive weights and unit row sums of `P`, the same weights are stationary for the
time-reversed matrix. See [Definition 1 (Quantum walk)][MagniezNayakRolandSantha2011]. -/
theorem timeReversal_stationary (P : Matrix X X ℝ) (π : X → ℝ)
    (hπ : ∀ x, 0 < π x) (hrow : ∀ x, ∑ y, P x y = 1) :
    ∀ y, ∑ x, π x * timeReversal P π x y = π y := by
  intro y
  have hterm : ∀ x, π x * timeReversal P π x y = π y * P y x := by
    intro x
    have hx : π x ≠ 0 := (hπ x).ne'
    rw [timeReversal_apply]
    field_simp
  calc
    ∑ x, π x * timeReversal P π x y = ∑ x, π y * P y x :=
      Finset.sum_congr rfl fun x _ => hterm x
    _ = π y * ∑ x, P y x := by rw [Finset.mul_sum]
    _ = π y := by rw [hrow y, mul_one]

/-- Time reversal relative to positive weights is involutive. -/
theorem timeReversal_involutive (P : Matrix X X ℝ) (π : X → ℝ)
    (hπ : ∀ x, 0 < π x) :
    timeReversal (timeReversal P π) π = P := by
  funext x y
  rw [timeReversal_apply, timeReversal_apply]
  have hx : π x ≠ 0 := (hπ x).ne'
  have hy : π y ≠ 0 := (hπ y).ne'
  field_simp

/-- The matrix whose `(x, y)` entry is the square root of `P x y * timeReversal P π y x`. -/
noncomputable def discriminant (P : Matrix X X ℝ) (π : X → ℝ) : Matrix X X ℝ :=
  fun x y => Real.sqrt (P x y * timeReversal P π y x)

/-- For nonnegative transitions and positive weights, each discriminant entry is `sqrt (π x) * P
x y / sqrt (π y)`. See [Definition 1 (Quantum walk)][MagniezNayakRolandSantha2011]. -/
theorem discriminant_eq_similarity (P : Matrix X X ℝ) (π : X → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (hπ : ∀ x, 0 < π x) :
    ∀ x y, discriminant P π x y = Real.sqrt (π x) * P x y / Real.sqrt (π y) := by
  intro x y
  have hx : Real.sqrt (π x) ≠ 0 := (Real.sqrt_pos.mpr (hπ x)).ne'
  have hy : Real.sqrt (π y) ≠ 0 := (Real.sqrt_pos.mpr (hπ y)).ne'
  have hprod : P x y * timeReversal P π y x
      = P x y ^ 2 * (π x / π y) := by
    rw [timeReversal_apply]
    field_simp
  have hsq : Real.sqrt (P x y ^ 2 * (π x / π y))
      = Real.sqrt (π x) * P x y / Real.sqrt (π y) := by
    rw [Real.sqrt_mul (sq_nonneg (P x y)), Real.sqrt_sq (hP x y),
      Real.sqrt_div (hπ x).le]
    ring
  rw [discriminant, hprod, hsq]

/-- Positive weights and detailed balance make the discriminant symmetric. -/
theorem discriminant_symm (P : Matrix X X ℝ) (π : X → ℝ)
    (hπ : ∀ x, 0 < π x)
    (hdb : ∀ x y, π x * P x y = π y * P y x) :
    ∀ x y, discriminant P π x y = discriminant P π y x := by
  intro x y
  have hPr : timeReversal P π = P := timeReversal_eq_of_detailedBalance P π hπ hdb
  have h1 : timeReversal P π y x = P y x := by rw [hPr]
  have h2 : timeReversal P π x y = P x y := by rw [hPr]
  simp only [discriminant, h1, h2, mul_comm]

end Qatlib.Papers.WalkSearch06.ReverseWalk.TimeReversal
