/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WaterLevel.WaterPrecision.CoherentReweightingDefs

/-!
# Error budgets and rational residual decisions

`TableBound` and `inputError` record bounded nonnegative tables and coordinatewise
perturbations. The fill, mass, and overlap error budgets feed `residualError`, while
`decideResidual` compares a rational residual with an uncertainty interval and returns a
positive, negative, or undecided result.

The clipped-fill quantities arise in quantum rejection sampling [OzolsRoettelerRoland2013], as
studied by [Ozols et al., 2013][OzolsRoettelerRoland2013].
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Concepts.WaterLevel.WaterPrecision
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

open Qatlib.Concepts.WaterLevel.WaterPrecision

/-- Requires every entry of both real tables to lie in the interval `[0, B]`. -/
def TableBound {m : ℕ} (p s : Fin m→ℝ) (B : ℝ) : Prop := ∀ i, 0≤p i ∧ p i≤B ∧ 0≤s i ∧ s i≤B

/-- Requires corresponding entries of the two source tables and the two target tables to differ
in absolute value by at most `δ`. -/
def inputError {m : ℕ} (p s p' s' : Fin m→ℝ) (δ : ℝ) : Prop := ∀ i, |p i-p' i|≤δ ∧ |s i-s' i|≤δ

/-- The fill perturbation budget `(1 + L) * δ` for levels bounded by `L`. -/
noncomputable def fillError (L δ : ℝ) : ℝ := (1+L)*δ
/-- The mass perturbation budget `2 * m * B * fillError L δ` for `m` bounded coordinates. -/
noncomputable def massError (m : ℕ) (B L δ : ℝ) : ℝ := 2*(m:ℝ)*B*fillError L δ
/-- The overlap perturbation budget `m * B * (fillError L δ + δ)`. -/
noncomputable def dotError (m : ℕ) (B L δ : ℝ) : ℝ := (m:ℝ)*B*(fillError L δ+δ)
/-- The real fidelity-threshold residual `realDot^2 - a * realMass` at the given level. -/
noncomputable def residual {m : ℕ} (p s : Fin m→ℝ) (γ a : ℝ) : ℝ := realDot p s γ^2-a*realMass p s γ

/-- The rational fidelity-threshold residual formed directly from the squared clipped-fill
overlap and the mass term weighted by `a`. -/
def residualRat {m : ℕ} (p s : Fin m→ℚ) (γ a : ℚ) : ℚ :=
  (∑ i, s i*min (p i) (γ*s i))^2-a*∑ i, (min (p i) (γ*s i))^2

/-- The rational residual-error budget combining `2 * m * B^2` times the overlap budget with
`|a|` times the mass budget. -/
def residualError (m : ℕ) (B L δ a : ℚ) : ℚ :=
  2*(m:ℚ)*B^2*((m:ℚ)*B*((1+L)*δ+δ))+|a| * (2*(m:ℚ)*B*((1+L)*δ))

/-- Returns `some true` when `q > e`, `some false` when the first test fails and `q < -e`, and
`none` otherwise. -/
def decideResidual (q e : ℚ) : Option Bool :=
    if e<q then some true else if q < -e then some false else none

end Qatlib.Concepts.WaterLevel.WaterPrecision
