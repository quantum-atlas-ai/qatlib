/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditResourceConverseAux

/-!
# The maximally entangled qudit teleportation contract

`QuditMaxEntResourceTeleportation` specifies unitary corrections for the branch Kraus operators
of an orthonormal-family resource. Scaling each adjoint branch operator by `n` gives a unitary
correction and makes the corrected branch equal to `1 / n²` times the identity map. The contract
concerns resource characterizations for teleportation [BennettEtAl1993Teleportation].

## Main statements

* `QuditMaxEntResourceTeleportation`: The proposition that each orthonormal-family qudit
  resource branch has unitary correction `n` times its adjoint and recovers every input operator
  with weight `1 / n²`.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QuditTeleport.ResourceIff
open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.QuditTeleport.QdLoccModel

open Matrix

/-- The proposition that each orthonormal-family qudit resource branch has unitary correction
`n` times its adjoint and recovers every input operator with weight `1 / n²`. -/
def QuditMaxEntResourceTeleportation : Prop :=
  ∀ (n : ℕ) [NeZero n] (u v : Fin n → QState (Fin n)),
    QuditOrthonormalFamily n u → QuditOrthonormalFamily n v →
    ∀ o : Fin n × Fin n,
      (((n : ℂ) • (quditResourceBranchKraus n (quditMaxEntResource n u v) o)ᴴ)
          ∈ Matrix.unitaryGroup (Fin n) ℂ) ∧
      ∀ ρ : Operator n,
        (((n : ℂ) • (quditResourceBranchKraus n (quditMaxEntResource n u v) o)ᴴ *
            quditResourceBranchKraus n (quditMaxEntResource n u v) o) * ρ *
          ((n : ℂ) • (quditResourceBranchKraus n (quditMaxEntResource n u v) o)ᴴ *
            quditResourceBranchKraus n (quditMaxEntResource n u v) o)ᴴ)
          = (1 / (n : ℂ) ^ 2) • ρ

end Qatlib.Concepts.QuditTeleport.QdLoccModel
