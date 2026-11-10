/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.ResetDiscard.Equation15Stat
import Qatlib.Concepts.ChannelTheory.Stinespring.PhyslibChannels
import Qatlib.Concepts.CoherentSim.ResetDiscard.Equation16Defs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding

namespace Qatlib.Concepts.CoherentSim.ResetDiscard

open Matrix
open scoped Matrix.Norms.L2Operator

def Equation16 : Prop :=
  ∀ (J I : Type*) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (W : Matrix (J × I) (J × I) ℂ) (j₀ : J) (X U : Matrix I I ℂ) (s δ₁ δ₂ : ℝ),
    IsBlockEncoding W j₀ X s → U ∈ Matrix.unitaryGroup I ℂ →
    ‖X - U‖ ≤ δ₁ → 1 ≤ s → |s - 2| ≤ δ₂ → δ₂ ≤ 1 →
    ∀ ψ : QState I, Normalized ψ →
    Matrix.traceNorm (ReducedState (vecOuter (FiberProjector j₀ *ᵥ
          (ObliviousAmplitudeAmplification (FiberProjector j₀) W *ᵥ TensorState (Ket j₀) ψ))) -
        ReducedState (vecOuter (TensorState (Ket j₀) (U *ᵥ ψ)))) ≤
      2 * ((15 + 12 * δ₁ + 4 * δ₁ ^ 2) * δ₁ + 15 * δ₂)

end Qatlib.Concepts.CoherentSim.ResetDiscard
