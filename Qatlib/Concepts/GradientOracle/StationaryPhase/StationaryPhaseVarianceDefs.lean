/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Data.Matrix.Basic

/-!
# Measure on the centered unit cube

`stationaryPhaseCube` defines the product of Lebesgue measures restricted to `[-1/2, 1/2]`. This
measure supplies the uniform cube moments used in the quadratic stationary-phase model
associated with [Jordan2005Gradient].

## Main definitions

* `stationaryPhaseCube`: the finite product measure for centered unit-interval coordinates.

## References

* [Jordan, 2005][Jordan2005Gradient]
-/

set_option autoImplicit false

open MeasureTheory

namespace Qatlib.Concepts.GradientOracle.StationaryPhase

/-- The product measure on real coordinate vectors with each factor given by Lebesgue measure
restricted to `[-1/2, 1/2]`. -/
noncomputable def stationaryPhaseCube (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ : Fin d => volume.restrict (Set.Icc (-1 / 2) (1 / 2 : ℝ))
end Qatlib.Concepts.GradientOracle.StationaryPhase
