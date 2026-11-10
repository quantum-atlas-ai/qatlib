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

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QChemistry14.ScalarModels.Definitions

open Real

def gaussOverlap (a b R : ℝ) : ℝ :=
  (Real.pi / (a + b)) ^ (3 / 2 : ℝ) * Real.exp (-(a * b / (a + b)) * R ^ 2)

def cutoffDistance (aMin : ℝ) (k : ℕ) : ℝ :=
  Real.sqrt (aMin⁻¹ * Real.log ((Real.pi / (2 * aMin)) ^ 3 * (10 : ℝ) ^ (2 * k)))

def rMax (Z N ρ : ℝ) : ℝ :=
  (3 * Z * N / (4 * Real.pi * ρ)) ^ (1 / 3 : ℝ)

def betaAB (ρ S Z : ℝ) : ℝ :=
  2 * Real.pi * ρ * S * (3 * Z / (4 * Real.pi * ρ)) ^ (2 / 3 : ℝ)

def nuclearEntryBound (ρ S Z N : ℝ) : ℝ :=
  2 * Real.pi * ρ * S * (rMax Z N ρ) ^ 2

end Qatlib.Papers.QChemistry14.ScalarModels.Definitions
