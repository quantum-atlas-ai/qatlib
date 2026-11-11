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
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Parameters for the localization gap estimate

This module defines the leading splitting, the threshold `lambdaStar`, the scale `N0`, the
density factor `vAlpha`, and the exponential expression `gapFormula`. Elementary identities for
real powers support the normalization identity `prefactor_pow_eight` used in the gap calculation
[AltshulerKroviRoland2010].

## Main statements

* `gapFormula`: defines the exponential gap expression.
* `prefactor_pow_eight`: identifies the eighth power of the prefactor with `N0`.

## References

* [Altshuler et al., 2010][AltshulerKroviRoland2010]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AndersonLoc09.MainResults

open Real

/-- The leading splitting expression `sqrt N * lam ^ 4 * f2`. -/
def leadingSplitting (N lam f2 : ℝ) : ℝ := Real.sqrt N * lam ^ 4 * f2

/-- The threshold expression `sqrt 2 * f2 ^ (-1 / 4) * N ^ (-1 / 8)`, using real powers. -/
def lambdaStar (N f2 : ℝ) : ℝ :=
  Real.sqrt 2 * Real.rpow f2 (-(1 / 4)) * Real.rpow N (-(1 / 8))

/-- The scale parameter `16 * A ^ 8 / f2 ^ 2`. -/
def N0 (A f2 : ℝ) : ℝ := 16 * A ^ 8 / f2 ^ 2

/-- The density factor `(4 / 9) * (1 - exp (-3 * α))`. -/
def vAlpha (α : ℝ) : ℝ := (4 / 9) * (1 - Real.exp (-3 * α))

/-- The exponential gap expression `exp (-(n / 8) * log (N / N0))`. -/
def gapFormula (n N N0 : ℝ) : ℝ := Real.exp (-(n / 8) * Real.log (N / N0))

/-- Raising a real power of a positive base to a natural power multiplies the real exponent by
that natural number. -/
theorem rpow_pow_nat (x : ℝ) (hx : 0 < x) (a : ℝ) (m : ℕ) :
    (Real.rpow x a) ^ m = Real.rpow x (a * (m : ℝ)) := by
  rw [← Real.rpow_natCast (Real.rpow x a) m]
  exact (Real.rpow_mul (le_of_lt hx) a (m : ℝ)).symm

/-- Negating a real exponent on a positive base gives the inverse of the original real power. -/
theorem rpow_neg_fn (x : ℝ) (hx : 0 < x) (a : ℝ) :
    Real.rpow x (-a) = (Real.rpow x a)⁻¹ :=
  Real.rpow_neg (le_of_lt hx) a

/-- A real power with a natural-number exponent agrees with the usual natural power. -/
theorem rpow_natcast_fn (x : ℝ) (n : ℕ) : Real.rpow x (n : ℝ) = x ^ n :=
  Real.rpow_natCast x n

/-- For a positive base, a real power of a sum of exponents is the product of the two real
powers. -/
theorem rpow_add_fn (x : ℝ) (hx : 0 < x) (a b : ℝ) :
    Real.rpow x (a + b) = Real.rpow x a * Real.rpow x b :=
  Real.rpow_add hx a b

/-- The zeroth real power of any real base equals one. -/
theorem rpow_zero_fn (x : ℝ) : Real.rpow x 0 = 1 :=
  Real.rpow_zero x

/-- For a positive base, a real power equals the exponential of the logarithm of the base times
the exponent. -/
theorem rpow_def_fn {x : ℝ} (hx : 0 < x) (y : ℝ) :
    Real.rpow x y = Real.exp (Real.log x * y) :=
  Real.rpow_def_of_pos hx y

/-- For positive `A` and `f2`, the eighth power of `A * sqrt 2 * f2 ^ (-1 / 4)` equals `N0 A f2`
[AltshulerKroviRoland2010]. -/
theorem prefactor_pow_eight (A f2 : ℝ) (hA : 0 < A) (hf2 : 0 < f2) :
    (A * Real.sqrt 2 * Real.rpow f2 (-(1 / 4))) ^ 8 = N0 A f2 := by
  unfold N0
  have h2 : (Real.sqrt 2) ^ 8 = 16 := by
    rw [show (Real.sqrt 2) ^ 8 = ((Real.sqrt 2) ^ 2) ^ 4 by ring,
      Real.sq_sqrt (by norm_num)]
    norm_num
  have hf : (Real.rpow f2 (-(1 / 4))) ^ 8 = (f2 ^ 2)⁻¹ := by
    rw [rpow_pow_nat f2 hf2 (-(1 / 4)) 8]
    rw [show (-(1 / 4 : ℝ) * ((8 : ℕ) : ℝ)) = -((2 : ℕ) : ℝ) by norm_num]
    rw [rpow_neg_fn f2 hf2 ((2 : ℕ) : ℝ), rpow_natcast_fn f2 2]
  have hexp : (A * Real.sqrt 2 * Real.rpow f2 (-(1 / 4))) ^ 8
      = A ^ 8 * (Real.sqrt 2) ^ 8 * (Real.rpow f2 (-(1 / 4))) ^ 8 := by ring
  rw [hexp, h2, hf]
  ring

end Qatlib.Papers.AndersonLoc09.MainResults
