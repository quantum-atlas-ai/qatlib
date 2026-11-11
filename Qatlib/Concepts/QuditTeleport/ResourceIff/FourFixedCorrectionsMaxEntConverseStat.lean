/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.ResourceIff.Eq9Aux

/-!
# The positive-resource four-correction marginal contract

`FourFixedCorrectionsMaxEntConverse` states that a positive semidefinite resource enabling exact
teleportation with four fixed unitary corrections has a maximally mixed receiver marginal. The
resource setting is the qubit teleportation protocol of [BennettEtAl1993Teleportation].

## Main statements

* `FourFixedCorrectionsMaxEntConverse`: The proposition that every positive semidefinite
  resource satisfying `FourFixedCorrectionsTeleport` has receiver marginal `(1 / 2) • 1`.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.QuditTeleport.ResourceIff

open scoped ComplexOrder

/-- The proposition that every positive semidefinite resource satisfying
`FourFixedCorrectionsTeleport` has receiver marginal `(1 / 2) • 1`. -/
def FourFixedCorrectionsMaxEntConverse : Prop :=
  ∀ (K : Fin 4 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (U : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ)
    (ω : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ),
    ω.PosSemidef → FourFixedCorrectionsTeleport K U ω →
    PartialTrace (relabelGate (Equiv.prodComm (Fin 2) (Fin 2)) ω)
      = (1 / 2 : ℂ) • (1 : Operator 2)

end Qatlib.Concepts.QuditTeleport.ResourceIff
