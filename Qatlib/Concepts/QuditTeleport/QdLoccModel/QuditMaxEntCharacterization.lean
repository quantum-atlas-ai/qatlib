/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditResourceConverseAux

/-!
# The qudit maximal-entanglement characterization contract

`QuditMaxEntCharacterization` combines two statements about pure bipartite qudit resources.
Orthonormal-family resources have both marginals equal to `1 / n` times the identity, and every
normalized pure state with this first marginal possesses such a resource representation. The
contract concerns resource characterizations for teleportation [BennettEtAl1993Teleportation].

## Main statements

* `QuditMaxEntCharacterization`: The proposition that orthonormal-family qudit resources have
  both maximally mixed marginals and that any normalized pure state with first marginal `(1 / n)
  • 1` has an orthonormal-family representation.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.QuditTeleport.ResourceIff

namespace Qatlib.Concepts.QuditTeleport.QdLoccModel

open Matrix

/-- The proposition that orthonormal-family qudit resources have both maximally mixed marginals
and that any normalized pure state with first marginal `(1 / n) • 1` has an
orthonormal-family representation. -/
def QuditMaxEntCharacterization : Prop :=
  (∀ (n : ℕ) [NeZero n] (u v : Fin n → QState (Fin n)),
    QuditOrthonormalFamily n u → QuditOrthonormalFamily n v →
    PartialTrace (outerProduct (quditMaxEntResource n u v))
      = (1 / (n : ℂ)) • (1 : Operator n) ∧
    PartialTrace (relabelGate (Equiv.prodComm (Fin n) (Fin n))
      (outerProduct (quditMaxEntResource n u v)))
      = (1 / (n : ℂ)) • (1 : Operator n)) ∧
  ∀ (n : ℕ) [NeZero n] (Ψ : QState (Fin n × Fin n)), Normalized Ψ →
    PartialTrace (outerProduct Ψ) = (1 / (n : ℂ)) • (1 : Operator n) →
    ∃ u v : Fin n → QState (Fin n),
      QuditOrthonormalFamily n u ∧ QuditOrthonormalFamily n v ∧
        quditMaxEntResource n u v = Ψ

end Qatlib.Concepts.QuditTeleport.QdLoccModel
