/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.BornMetrics.FiniteStats.Defs

/-!
# Mass-scaled sphere and simplex measures

This module defines `normalizeByMass`, which scales a measure by the inverse of its total mass.
It applies that construction to the spherical measure induced by Euclidean volume in real
dimension `2 * m` and to Hausdorff measure of dimension `N - 1` on `simplex N`.

The declarations specify the scaled measures; their definitions alone do not establish finite
positive total mass. Such geometric measures support volume comparisons in quantum circuit
approximation [Knill1995].

## Main statements

* `normalizeByMass`: Scale a measure by the inverse of its total mass, using extended
  nonnegative real arithmetic.
* `sphereProb`: The measure on the unit sphere in real dimension `2 * m` obtained by applying
  `normalizeByMass` to the spherical measure induced by Euclidean volume.
* `simplexProb`: The measure on `simplex N` obtained by applying `normalizeByMass` to Hausdorff
  measure of dimension `(N - 1 : ℕ)`.

## References

* [Knill, 1995][Knill1995]
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open Qatlib.Foundations.BornMetrics.FiniteStats
open scoped BigOperators
namespace Qatlib.Foundations.FrameMeasures.HaarFrames

/-- Scale a measure by the inverse of its total mass, using extended nonnegative real
arithmetic. -/
def normalizeByMass {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α) :
    MeasureTheory.Measure α := (μ Set.univ)⁻¹ • μ

/-- The measure on the unit sphere in real dimension `2 * m` obtained by applying
`normalizeByMass` to the spherical measure induced by Euclidean volume. -/
def sphereProb (m : ℕ) :
    MeasureTheory.Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin (2 * m))) 1) :=
  normalizeByMass (MeasureTheory.Measure.toSphere (volume : MeasureTheory.Measure
    (EuclideanSpace ℝ (Fin (2 * m)))))

/-- The measure on `simplex N` obtained by applying `normalizeByMass` to Hausdorff measure of
dimension `(N - 1 : ℕ)`. -/
def simplexProb (N : ℕ) : MeasureTheory.Measure (simplex N) :=
  normalizeByMass (MeasureTheory.Measure.hausdorffMeasure ((N - 1 : ℕ) : ℝ))

end Qatlib.Foundations.FrameMeasures.HaarFrames
