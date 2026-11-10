/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.ResetDiscard.ObliviousAmplitudeAmplification
import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.Tensor
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding

namespace Qatlib.Concepts.CoherentSim.ResetDiscard

open Matrix

def Equation14 : Prop :=
  ∀ (J I : Type*) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (W : Matrix (J × I) (J × I) ℂ) (j₀ : J) (U : Matrix I I ℂ) (s : ℝ),
    IsBlockEncoding W j₀ U s → ∀ (ψ : QState I),
    FiberProjector j₀ *ᵥ
      (ObliviousAmplitudeAmplification (FiberProjector j₀) W *ᵥ TensorState (Ket j₀) ψ) =
      TensorState (Ket j₀)
        (((((3 / s : ℝ) : ℂ) • U) - (((4 / s ^ 3 : ℝ) : ℂ) • (U * Uᴴ * U))) *ᵥ ψ)

end Qatlib.Concepts.CoherentSim.ResetDiscard
