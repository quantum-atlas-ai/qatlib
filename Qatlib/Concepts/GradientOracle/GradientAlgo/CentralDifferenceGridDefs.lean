/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.CentralDiff.CentralDifferenceExactnessStat
import Qatlib.Concepts.GradientOracle.GradientAlgo.TensorChebyshevGridBoundStat

/-!
# Centered finite grids

`gridCenter` defines equally spaced cell centers in a real interval, and `gridPoint` assembles
them into Euclidean vectors. These grids provide evaluation points for the central-difference
gradient analysis associated with [GilyenArunachalamWiebe2019].

## Main definitions

* `gridCenter`: the coordinate `R * ((2*z+1)/(2*M) - 1/2)`.
* `gridPoint`: the Euclidean vector of centered grid coordinates.

## References

* [Gilyen, Arunachalam and Wiebe, 2019][GilyenArunachalamWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.GradientOracle.CentralDiff

namespace Qatlib.Concepts.GradientOracle.GradientAlgo
noncomputable section

/-- The real coordinate `R * ((2*z+1)/(2*M) - 1/2)` of the indexed cell center in the centered
interval of scale `R`. -/
noncomputable def gridCenter (M : ℕ) (R : ℝ) (z : Fin M) : ℝ :=
  R * ((2 * (z : ℝ) + 1) / (2 * M) - 1 / 2)
end
noncomputable section

/-- The Euclidean vector whose coordinates are the centered grid values `gridCenter M R (z j)`. -/
noncomputable def gridPoint (d M : ℕ) (R : ℝ) (z : Fin d → Fin M) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j : Fin d => gridCenter M R (z j))
end
end Qatlib.Concepts.GradientOracle.GradientAlgo
