/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditResourceConverseAux

/-!
# The qudit resource marginal converse contract

`QuditResourceMarginalConverse` requires the receiver marginal of a positive semidefinite
resource enabling perfect fixed-correction qudit teleportation to equal `1 / n` times the
identity. The receiver marginal is expressed using a swap followed by `PartialTrace`. The
contract concerns resource characterizations for teleportation [BennettEtAl1993Teleportation].

## Main statements

* `QuditResourceMarginalConverse`: The proposition that every positive semidefinite resource
  satisfying `QuditFixedCorrectionsTeleport` has receiver marginal `(1 / n) • 1`.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.QuditTeleport.ResourceIff

namespace Qatlib.Concepts.QuditTeleport.QdLoccModel

open scoped ComplexOrder

/-- The proposition that every positive semidefinite resource satisfying
`QuditFixedCorrectionsTeleport` has receiver marginal `(1 / n) • 1`. -/
def QuditResourceMarginalConverse : Prop :=
  ∀ (n : ℕ) [NeZero n]
    (K : Fin n × Fin n → Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (U : Fin n × Fin n → Operator n)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ),
    ω.PosSemidef → QuditFixedCorrectionsTeleport n K U ω →
    PartialTrace (relabelGate (Equiv.prodComm (Fin n) (Fin n)) ω)
      = (1 / (n : ℂ)) • (1 : Operator n)

end Qatlib.Concepts.QuditTeleport.QdLoccModel
