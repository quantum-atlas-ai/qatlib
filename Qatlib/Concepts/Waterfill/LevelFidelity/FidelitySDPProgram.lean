/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Waterfill.LevelFidelity.PsdOverlapDiagonal
import Qatlib.Concepts.Waterfill.LevelFidelity.FidelityLevelSubgoalQuan
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.Waterfill.LevelFidelity.WaterLevelFidelity

namespace Qatlib.Concepts.Waterfill.LevelFidelity

def sourceWaterMatrix {m : ℕ} (π σ : Fin m → ℚ) (γ : ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => (levelFill π σ γ i : ℂ) * (levelFill π σ γ j : ℂ)

end Qatlib.Concepts.Waterfill.LevelFidelity
