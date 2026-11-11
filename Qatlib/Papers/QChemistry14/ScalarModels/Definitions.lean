/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Tactic

/-!
# Scalar Gaussian and nuclear-attraction models

This module defines the closed scalar Gaussian overlap and its logarithmic cutoff distance. It
also defines the uniform-ball radius and nuclear-attraction expressions used in the subsequent
size-scaling comparisons. See [McCleanEtAl2014].

## Main statements

* `gaussOverlap`: The scalar overlap formula `(π / (a + b))^(3/2) * exp (-(a * b / (a + b)) *
  R²)`.
* `cutoffDistance`: The square root of `aMin⁻¹ * log ((π / (2 * aMin))³ * 10^(2 * k))`, used as
  the scalar overlap cutoff radius.
* `nuclearEntryBound`: The scalar nuclear-entry bound `2 * π * ρ * S * (rMax Z N ρ)²`.

## References

* [McClean et al., 2014][McCleanEtAl2014]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QChemistry14.ScalarModels.Definitions

open Real

/-- The scalar overlap formula `(π / (a + b))^(3/2) * exp (-(a * b / (a + b)) * R²)`. -/
def gaussOverlap (a b R : ℝ) : ℝ :=
  (Real.pi / (a + b)) ^ (3 / 2 : ℝ) * Real.exp (-(a * b / (a + b)) * R ^ 2)

/-- The square root of `aMin⁻¹ * log ((π / (2 * aMin))³ * 10^(2 * k))`, used as the scalar
overlap cutoff radius. -/
def cutoffDistance (aMin : ℝ) (k : ℕ) : ℝ :=
  Real.sqrt (aMin⁻¹ * Real.log ((Real.pi / (2 * aMin)) ^ 3 * (10 : ℝ) ^ (2 * k)))

/-- The real-power radius `(3 * Z * N / (4 * π * ρ))^(1/3)` of the uniform-ball model. -/
def rMax (Z N ρ : ℝ) : ℝ :=
  (3 * Z * N / (4 * Real.pi * ρ)) ^ (1 / 3 : ℝ)

/-- The scalar nuclear-attraction prefactor `2 * π * ρ * S * (3 * Z / (4 * π * ρ))^(2/3)`. -/
def betaAB (ρ S Z : ℝ) : ℝ :=
  2 * Real.pi * ρ * S * (3 * Z / (4 * Real.pi * ρ)) ^ (2 / 3 : ℝ)

/-- The scalar nuclear-entry bound `2 * π * ρ * S * (rMax Z N ρ)²`. -/
def nuclearEntryBound (ρ S Z N : ℝ) : ℝ :=
  2 * Real.pi * ρ * S * (rMax Z N ρ) ^ 2

end Qatlib.Papers.QChemistry14.ScalarModels.Definitions
