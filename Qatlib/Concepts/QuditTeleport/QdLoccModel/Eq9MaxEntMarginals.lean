/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.ResourceIff.Eq9Aux

/-!
# The Eq. (9) marginal contract

`Eq9MaxEntMarginals` states that a resource built from two orthonormal qubit pairs has both
reduced operators equal to half the identity. The second reduction is expressed by swapping the
tensor factors before taking `PartialTrace`. The contract concerns resource characterizations
for teleportation [BennettEtAl1993Teleportation].

## Main statements

* `Eq9MaxEntMarginals`: The proposition that both one-qubit marginals of every resource
  `eq9Resource` built from orthonormal pairs equal `(1 / 2) • 1`.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.QuditTeleport.ResourceIff

namespace Qatlib.Concepts.QuditTeleport.QdLoccModel

/-- The proposition that both one-qubit marginals of every resource `eq9Resource` built from
orthonormal pairs equal `(1 / 2) • 1`. -/
def Eq9MaxEntMarginals : Prop :=
  ∀ (u v p q : QState (Fin 2)), eq9OrthoPairs u v p q →
    PartialTrace (outerProduct (eq9Resource u v p q)) = (1 / 2 : ℂ) • (1 : Operator 2) ∧
    PartialTrace (relabelGate (Equiv.prodComm (Fin 2) (Fin 2))
      (outerProduct (eq9Resource u v p q))) = (1 / 2 : ℂ) • (1 : Operator 2)

end Qatlib.Concepts.QuditTeleport.QdLoccModel
