/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.ResetDiscard.ObliviousAmplitudeAmplification
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Complex.Basic
set_option warningAsError false

namespace Qatlib.Concepts.CoherentSim.ResetDiscard

open Matrix

def Equation13 : Prop :=
  ∀ (I : Type*) [Fintype I] [DecidableEq I]
    (P W : Matrix I I ℂ), IsStarProjection P → W ∈ Matrix.unitaryGroup I ℂ →
    ∀ (ψ : I → ℂ), P *ᵥ ψ = ψ →
    P *ᵥ (ObliviousAmplitudeAmplification P W *ᵥ ψ) =
      (3 * (P * W) - 4 * (P * W * P * Wᴴ * P * W)) *ᵥ ψ

end Qatlib.Concepts.CoherentSim.ResetDiscard
