/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.ResetDiscard.ObliviousAmplitudeAmplification
import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.Tensor

/-!
# Statement of scaled cubic amplification

`Equation14` specifies the selected-fiber output of oblivious amplification for an arbitrary
scaled block encoding. Its coefficients `3 / s` and `4 / s³` describe the cubic amplification
polynomial of [BerryEtAl2015Taylor].

## Main statements

* `Equation14`: The proposition specifying the scaled cubic output.

## References

* [Berry et al., 2015][BerryEtAl2015Taylor]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding

namespace Qatlib.Concepts.CoherentSim.ResetDiscard

open Matrix

/-- The proposition that projecting the amplified output of a scale-`s` encoding onto its
ancillary fiber gives the cubic operator `(3 / s) • U - (4 / s³) • (U * Uᴴ * U)` on the data
vector. -/
def Equation14 : Prop :=
  ∀ (J I : Type*) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (W : Matrix (J × I) (J × I) ℂ) (j₀ : J) (U : Matrix I I ℂ) (s : ℝ),
    IsBlockEncoding W j₀ U s → ∀ (ψ : QState I),
    FiberProjector j₀ *ᵥ
      (ObliviousAmplitudeAmplification (FiberProjector j₀) W *ᵥ TensorState (Ket j₀) ψ) =
      TensorState (Ket j₀)
        (((((3 / s : ℝ) : ℂ) • U) - (((4 / s ^ 3 : ℝ) : ℂ) • (U * Uᴴ * U))) *ᵥ ψ)

end Qatlib.Concepts.CoherentSim.ResetDiscard
