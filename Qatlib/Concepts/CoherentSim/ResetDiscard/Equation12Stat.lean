/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.ResetDiscard.ObliviousAmplitudeAmplification
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding

namespace Qatlib.Concepts.CoherentSim.ResetDiscard

open Matrix

def Equation12 : Prop :=
  ∀ (J I : Type*) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (W : Matrix (J × I) (J × I) ℂ) (j₀ : J) (U : Matrix I I ℂ),
    IsBlockEncoding W j₀ U 2 → U ∈ Matrix.unitaryGroup I ℂ → ∀ (ψ : QState I),
    ObliviousAmplitudeAmplification (FiberProjector j₀) W *ᵥ TensorState (Ket j₀) ψ =
      TensorState (Ket j₀) (U *ᵥ ψ)

end Qatlib.Concepts.CoherentSim.ResetDiscard
