/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.ResourceIff.Eq9Aux
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.QuditTeleport.ResourceIff

def FourFixedCorrectionsMaxEntConverseCore : Prop :=
  ∀ (K : Fin 4 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (U : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ)
    (ω : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ),
    FourFixedCorrectionsTeleport K U ω →
    PartialTrace (relabelGate (Equiv.prodComm (Fin 2) (Fin 2)) ω)
      = (1 / 2 : ℂ) • (1 : Operator 2)

end Qatlib.Concepts.QuditTeleport.ResourceIff
