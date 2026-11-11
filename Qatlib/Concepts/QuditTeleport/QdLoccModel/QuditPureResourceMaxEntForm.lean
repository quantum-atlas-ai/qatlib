/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditResourceConverseAux

/-!
# The pure qudit teleportation resource contract

`QuditPureResourceMaxEntForm` states a necessary resource form for perfect qudit teleportation
with fixed unitary corrections. A normalized pure resource must be representable as an equally
weighted sum of tensor products from two orthonormal families. The contract concerns resource
characterizations for teleportation [BennettEtAl1993Teleportation].

## Main statements

* `QuditPureResourceMaxEntForm`: The proposition that a normalized pure resource enabling
  `QuditFixedCorrectionsTeleport` has the form `quditMaxEntResource n u v` for two orthonormal
  families.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option warningAsError false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QuditTeleport.ResourceIff

namespace Qatlib.Concepts.QuditTeleport.QdLoccModel

/-- The proposition that a normalized pure resource enabling `QuditFixedCorrectionsTeleport` has
the form `quditMaxEntResource n u v` for two orthonormal families. -/
def QuditPureResourceMaxEntForm : Prop :=
  ∀ (n : ℕ) [NeZero n]
    (K : Fin n × Fin n → Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (U : Fin n × Fin n → Operator n) (Ψ : QState (Fin n × Fin n)),
    Normalized Ψ →
    QuditFixedCorrectionsTeleport n K U (outerProduct Ψ) →
    ∃ u v : Fin n → QState (Fin n),
      QuditOrthonormalFamily n u ∧ QuditOrthonormalFamily n v ∧
        quditMaxEntResource n u v = Ψ

end Qatlib.Concepts.QuditTeleport.QdLoccModel
