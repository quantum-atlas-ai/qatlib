/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Data.Matrix.Basic
import Qatlib.Concepts.GradientOracle.StationaryPhase.StationaryPhaseVarianceDefs

/-!
# Specification of stationary-phase variance formulas

`StationaryPhaseVariance` packages exact uniform-cube moment identities and their rescaling for
a real matrix. It formalizes the variance calculation in the quadratic stationary-phase model
associated with [Jordan2005Gradient].

## Main statements

* `StationaryPhaseVariance`: covariance `1/12` on equal coordinates, row-norm variance formulas,
  and the resulting dimension-dependent bound.

## References

* [Jordan, 2005][Jordan2005Gradient]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.GradientOracle.StationaryPhase

open MeasureTheory

/-- The conjunction of centered-cube mean and covariance identities, matrix-row second moments,
physical-unit rescaling formulas, and the standard-deviation bound from entrywise matrix
control. -/
def StationaryPhaseVariance : Prop :=
  (∀ (d : ℕ) (i : Fin d), ∫ u, u i ∂stationaryPhaseCube d = 0) ∧
  (∀ (d : ℕ) (i j : Fin d),
      ∫ u, u i * u j ∂stationaryPhaseCube d = if i = j then 1 / 12 else 0) ∧
  (∀ (d : ℕ) (A : Matrix (Fin d) (Fin d) ℝ) (i : Fin d),
      ∫ u, ∑ j, A i j * u j ∂stationaryPhaseCube d = 0 ∧
      ∫ u, (∑ j, A i j * u j) ^ 2 ∂stationaryPhaseCube d = (1 / 12) * ∑ j, (A i j) ^ 2) ∧
  (∀ (d n : ℕ) (l m : ℝ) (H : Matrix (Fin d) (Fin d) ℝ) (i : Fin d),
      0 < l → 0 < m →
      ∫ u, (∑ j, (2 ^ n : ℝ) * l / m * H i j * u j) ^ 2 ∂stationaryPhaseCube d =
        (2 ^ n : ℝ) ^ 2 * l ^ 2 / (12 * m ^ 2) * ∑ j, (H i j) ^ 2 ∧
      (m / (2 ^ n : ℝ)) * Real.sqrt ((2 ^ n : ℝ) ^ 2 * l ^ 2 / (12 * m ^ 2) * ∑ j, (H i j) ^ 2) =
        l / (2 * Real.sqrt 3) * Real.sqrt (∑ j, (H i j) ^ 2)) ∧
  (∀ (d _n : ℕ) (l m D : ℝ) (H : Matrix (Fin d) (Fin d) ℝ) (i : Fin d),
      0 < l → 0 < m → 0 ≤ D → (∀ i j, |H i j| ≤ D) →
      l / (2 * Real.sqrt 3) * Real.sqrt (∑ j, (H i j) ^ 2) ≤ l * D * Real.sqrt d / (2 * Real.sqrt 3))

end Qatlib.Concepts.GradientOracle.StationaryPhase
