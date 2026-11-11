/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.ResetDiscard.ObliviousAmplitudeAmplification
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Complex.Basic

/-!
# Statement of the projected cubic identity

`Equation13` states the action of projected oblivious amplification as a linear term minus a
cubic term. It assumes a star projection, a unitary matrix, and an input vector in the
projection range, as in the amplification analysis of [BerryEtAl2015Taylor].

## Main statements

* `Equation13`: The proposition specifying the projected cubic action.

## References

* [Berry et al., 2015][BerryEtAl2015Taylor]
-/

set_option warningAsError false

namespace Qatlib.Concepts.CoherentSim.ResetDiscard

open Matrix

/-- The proposition that projected oblivious amplification acts on vectors fixed by the
projection as `3 * (P * W) - 4 * (P * W * P * Wᴴ * P * W)`. -/
def Equation13 : Prop :=
  ∀ (I : Type*) [Fintype I] [DecidableEq I]
    (P W : Matrix I I ℂ), IsStarProjection P → W ∈ Matrix.unitaryGroup I ℂ →
    ∀ (ψ : I → ℂ), P *ᵥ ψ = ψ →
    P *ᵥ (ObliviousAmplitudeAmplification P W *ᵥ ψ) =
      (3 * (P * W) - 4 * (P * W * P * Wᴴ * P * W)) *ᵥ ψ

end Qatlib.Concepts.CoherentSim.ResetDiscard
