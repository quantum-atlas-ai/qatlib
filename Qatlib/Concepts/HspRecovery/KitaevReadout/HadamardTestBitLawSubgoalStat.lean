/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.KitaevReadout.EigenphaseHadamardTest
set_option warningAsError false

open Matrix
open scoped Classical

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.HspRecovery.KitaevReadout

def HadamardTestBitLawSubgoal : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (U : Matrix I I ℂ) (ψ : QState I) (φ : ℝ),
    (U *ᵥ ψ = eigenPhase φ • ψ) →
    ApplyGate (hadamardTestGate I U) (TensorState ψ (Ket false))
      = TensorState ψ (hadamardTestBitState (eigenPhase φ))
    ∧ BornProb (hadamardTestBitState (eigenPhase φ)) false
        = (1 + Real.cos (2 * Real.pi * φ)) / 2
    ∧ BornProb (hadamardTestBitState (eigenPhase φ)) true
        = (1 - Real.cos (2 * Real.pi * φ)) / 2

end Qatlib.Concepts.HspRecovery.KitaevReadout
