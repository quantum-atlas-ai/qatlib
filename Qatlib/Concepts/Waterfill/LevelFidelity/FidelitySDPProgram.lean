/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Waterfill.LevelFidelity.PsdOverlapDiagonal
import Qatlib.Concepts.Waterfill.LevelFidelity.FidelityLevelSubgoalQuan

/-!
# Water-filling matrices for fidelity optimization

`sourceWaterMatrix` forms the complex outer-product matrix of the real water-filling profile
`levelFill`. This matrix supplies the candidate used in semidefinite formulations of
source-constrained fidelity optimization for quantum rejection sampling
[OzolsRoettelerRoland2013].

## Main statements

* `sourceWaterMatrix`: define the matrix with entries given by products of water-filled
  amplitudes.

## References

* [Ozols et al., 2013][OzolsRoettelerRoland2013]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.Waterfill.LevelFidelity.WaterLevelFidelity

namespace Qatlib.Concepts.Waterfill.LevelFidelity

/-- The complex matrix with entry `(i, j)` equal to the product of the real water-filled
amplitudes at coordinates `i` and `j`. -/
def sourceWaterMatrix {m : ℕ} (π σ : Fin m → ℚ) (γ : ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => (levelFill π σ γ i : ℂ) * (levelFill π σ γ j : ℂ)

end Qatlib.Concepts.Waterfill.LevelFidelity
