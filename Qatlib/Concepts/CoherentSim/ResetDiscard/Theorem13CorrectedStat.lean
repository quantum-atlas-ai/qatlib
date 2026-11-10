/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.LinearCombination
import Qatlib.Concepts.CoherentSim.ResetDiscard.Theorem13Figure3Defs
set_option warningAsError false
open Qatlib.Foundations.PureStateMath

open Matrix

namespace Qatlib.Concepts.CoherentSim.ResetDiscard

def Theorem13Corrected : Prop :=
  ∀ (J I : Type) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (U : J → Matrix I I ℂ), (∀ m, U m ∈ Matrix.unitaryGroup I ℂ) →
    ∀ (C : J → ℂ), 0 < ∑ m, ‖C m‖ →
    ∀ (A : Matrix J J ℂ), A ∈ Matrix.unitaryGroup J ℂ →
    ∀ (B : Matrix J J ℂ), B ∈ Matrix.unitaryGroup J ℂ →
    ∀ (j₀ : J) (K : ℂ), (∀ m, B j₀ m * A m j₀ = K * C m) →
    ∀ ψ : QState I, Normalized ψ →
      Fig3SuccessProb U A B j₀ ψ
        ≤ (∑ i, ‖((∑ m, C m • U m) *ᵥ ψ) i‖ ^ 2) / (∑ m, ‖C m‖) ^ 2

end Qatlib.Concepts.CoherentSim.ResetDiscard
