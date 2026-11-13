/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.ResourceIff.Eq9Aux

/-!
# The Eq. (9) pure-resource characterization contract

`Eq9MaxEntCharacterization` states that a normalized bipartite qubit vector with first marginal
equal to half the identity has the two-orthonormal-pair form `eq9Resource`. The resource setting
is the qubit teleportation protocol of [BennettEtAl1993Teleportation].

## Main statements

* `Eq9MaxEntCharacterization`: The proposition that every normalized pure two-qubit state with
  first marginal `(1 / 2) • 1` equals `eq9Resource u v p q` for two orthonormal pairs.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QuditTeleport.ResourceIff

/-- The proposition that every normalized pure two-qubit state with first marginal `(1 / 2) • 1`
equals `eq9Resource u v p q` for two orthonormal pairs. -/
def Eq9MaxEntCharacterization : Prop :=
  ∀ (Ψ : QState (Fin 2 × Fin 2)), Normalized Ψ →
    PartialTrace (outerProduct Ψ) = (1 / 2 : ℂ) • (1 : Operator 2) →
    ∃ u v p q : QState (Fin 2), eq9OrthoPairs u v p q ∧ eq9Resource u v p q = Ψ

end Qatlib.Concepts.QuditTeleport.ResourceIff
