/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.ResetDiscard.ResetDiscardDefinitions

/-!
# Statement of amplified reset-and-discard segmentation

`ResetDiscardSegmentationCorrected` states a trace-norm error bound for iterating the amplified
reset-and-discard map. It compares against conjugation by the full unitary power and records
linear error accumulation in the Taylor amplification setting [BerryEtAl2015Taylor].

## Main statements

* `ResetDiscardSegmentationCorrected`: The proposition specifying the corrected iteration bound.

## References

* [Berry et al., 2015][BerryEtAl2015Taylor]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.BlockEncoding.StateBlockEncoding

namespace Qatlib.Concepts.CoherentSim.ResetDiscard
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

/-- The proposition that `r` corrected reset-and-discard steps differ from conjugation by `U^r`
by at most `4 * r * ((15 + 12 * δ₁ + 4 * δ₁²) * δ₁ + 15 * δ₂)` in trace norm on density
operators under the stated encoding assumptions. -/
def ResetDiscardSegmentationCorrected : Prop :=
  ∀ (J I : Type*) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (W : Matrix (J × I) (J × I) ℂ) (j₀ : J) (X U : Matrix I I ℂ) (s δ₁ δ₂ : ℝ) (r : ℕ),
    IsBlockEncoding W j₀ X s → U ∈ Matrix.unitaryGroup I ℂ →
    ‖X - U‖ ≤ δ₁ → 1 ≤ s → |s - 2| ≤ δ₂ → δ₂ ≤ 1 →
    ∀ ρ : Matrix I I ℂ, ρ.PosSemidef → Matrix.trace ρ = 1 →
    Matrix.traceNorm ((ResetDiscardStepCorrected W j₀)^[r] ρ -
        U ^ r * ρ * (Uᴴ)^r) ≤
      4 * r * ((15 + 12 * δ₁ + 4 * δ₁ ^ 2) * δ₁ + 15 * δ₂)

end Qatlib.Concepts.CoherentSim.ResetDiscard
