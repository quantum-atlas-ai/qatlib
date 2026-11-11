/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs

/-!
# The stationary-weight discriminant matrix

This module defines `mnrsDiscriminant`, the complex matrix with entries `√(π x) * P x y / √(π
y)`. It supplies the stationary-weight similarity expression used in the quantum-walk framework
of [MagniezNayakRolandSantha2011]; the definition itself imposes no positivity or stationarity
assumptions.

## Main declarations

* `mnrsDiscriminant`: the discriminant expression associated with a real matrix and a weight
  function.

## References

* [Magniez et al., 2011][MagniezNayakRolandSantha2011]
-/

open scoped BigOperators

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

/-- The complex matrix whose `(x, y)` entry is the real quantity `√(π x) * P x y / √(π y)` cast
to `ℂ`. -/
noncomputable def mnrsDiscriminant {X : Type*}
    (P : Matrix X X ℝ) (π : X → ℝ) : Matrix X X ℂ :=
  fun x y => ((Real.sqrt (π x) * P x y / Real.sqrt (π y) : ℝ) : ℂ)

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
