/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.ResetDiscard.Equation14Stat
import Qatlib.Foundations.OperatorErrors.OperatorError
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Statement of amplified vector-error control

`Equation15` states a quantitative vector-error estimate for projected oblivious amplification.
It separates the encoded-operator error from the deviation of the encoding scale from two, in
the robustness setting of [BerryEtAl2015Taylor].

## Main statements

* `Equation15`: The proposition specifying the projected amplified error bound.

## References

* [Berry et al., 2015][BerryEtAl2015Taylor]
-/

set_option warningAsError false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding

namespace Qatlib.Concepts.CoherentSim.ResetDiscard

open Matrix
open scoped Matrix.Norms.L2Operator

/-- The proposition that an encoded operator error `δ₁` and a scale deviation `δ₂` yield
projected amplified vector error at most `(15 + 12 * δ₁ + 4 * δ₁²) * δ₁ + 15 * δ₂` for
normalized inputs, subject to the stated scale bounds. -/
def Equation15 : Prop :=
  ∀ (J I : Type*) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (W : Matrix (J × I) (J × I) ℂ) (j₀ : J) (X U : Matrix I I ℂ) (s δ₁ δ₂ : ℝ),
    IsBlockEncoding W j₀ X s → U ∈ Matrix.unitaryGroup I ℂ →
    ‖X - U‖ ≤ δ₁ → 1 ≤ s → |s - 2| ≤ δ₂ → δ₂ ≤ 1 →
    ∀ ψ : QState I, Normalized ψ →
    ‖toEuclidean_fromVec (FiberProjector j₀ *ᵥ
        (ObliviousAmplitudeAmplification (FiberProjector j₀) W *ᵥ TensorState (Ket j₀) ψ) -
        TensorState (Ket j₀) (U *ᵥ ψ))‖ ≤
      (15 + 12 * δ₁ + 4 * δ₁ ^ 2) * δ₁ + 15 * δ₂

end Qatlib.Concepts.CoherentSim.ResetDiscard
