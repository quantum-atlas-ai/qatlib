/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.ResetDiscard.ObliviousAmplitudeAmplification
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic

/-!
# Statement of exact oblivious amplification

`Equation12` specifies exact unitary action after oblivious amplification of a scale-two block
encoding. The statement is formulated on embedded state vectors, following the amplification
identity in [BerryEtAl2015Taylor].

## Main statements

* `Equation12`: The proposition specifying exact amplified action.

## References

* [Berry et al., 2015][BerryEtAl2015Taylor]
-/

set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding

namespace Qatlib.Concepts.CoherentSim.ResetDiscard

open Matrix

/-- The proposition that oblivious amplification of a scale-two block encoding of a unitary maps
each embedded input vector to the embedded unitary output. -/
def Equation12 : Prop :=
  ∀ (J I : Type*) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (W : Matrix (J × I) (J × I) ℂ) (j₀ : J) (U : Matrix I I ℂ),
    IsBlockEncoding W j₀ U 2 → U ∈ Matrix.unitaryGroup I ℂ → ∀ (ψ : QState I),
    ObliviousAmplitudeAmplification (FiberProjector j₀) W *ᵥ TensorState (Ket j₀) ψ =
      TensorState (Ket j₀) (U *ᵥ ψ)

end Qatlib.Concepts.CoherentSim.ResetDiscard
