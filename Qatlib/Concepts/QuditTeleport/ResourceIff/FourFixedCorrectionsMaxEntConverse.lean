/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.ResourceIff.Eq9Aux

/-!
# The unrestricted four-correction marginal contract

`FourFixedCorrectionsMaxEntConverseCore` states a receiver-marginal converse for an arbitrary
resource matrix satisfying `FourFixedCorrectionsTeleport`. This formulation does not require the
resource to be positive semidefinite. The resource setting is the qubit teleportation protocol
of [BennettEtAl1993Teleportation].

## Main statements

* `FourFixedCorrectionsMaxEntConverseCore`: The proposition that any resource matrix enabling
  four fixed unitary corrections has receiver marginal `(1 / 2) • 1`, without a positivity
  hypothesis on the resource.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.QuditTeleport.ResourceIff

/-- The proposition that any resource matrix enabling four fixed unitary corrections has
receiver marginal `(1 / 2) • 1`, without a positivity hypothesis on the resource. -/
def FourFixedCorrectionsMaxEntConverseCore : Prop :=
  ∀ (K : Fin 4 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (U : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ)
    (ω : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ),
    FourFixedCorrectionsTeleport K U ω →
    PartialTrace (relabelGate (Equiv.prodComm (Fin 2) (Fin 2)) ω)
      = (1 / 2 : ℂ) • (1 : Operator 2)

end Qatlib.Concepts.QuditTeleport.ResourceIff
