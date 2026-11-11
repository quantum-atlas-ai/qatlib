/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.ResourceIff.Eq9Aux

/-!
# The Eq. (9) resource teleportation contract

`Eq9ResourceTeleportation` specifies corrections for the teleportation branches of a
Boolean-indexed two-pair resource. For orthonormal pairs, twice the adjoint of each branch Kraus
operator is unitary and gives corrected branch weight one quarter. The resource setting is the
qubit teleportation protocol of [BennettEtAl1993Teleportation].

## Main statements

* `Eq9ResourceTeleportation`: The proposition that an orthonormal two-pair resource has unitary
  branch corrections `2 • Kᴴ` and each corrected branch sends every input `ρ` to `(1 / 4) • ρ`.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QuditTeleport.ResourceIff

open Matrix

/-- The proposition that an orthonormal two-pair resource has unitary branch corrections `2 •
Kᴴ` and each corrected branch sends every input `ρ` to `(1 / 4) • ρ`. -/
def Eq9ResourceTeleportation : Prop :=
  ∀ (u v p q : QState Bool), eq9OrthoPairsB u v p q →
    ∀ o : Bool × Bool,
      (((2 : ℂ) • (eq9BranchKraus u v p q o)ᴴ) ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧
      ∀ ρ : Operator 2,
        ((2 : ℂ) • (eq9BranchKraus u v p q o)ᴴ * eq9BranchKraus u v p q o) * ρ *
          ((2 : ℂ) • (eq9BranchKraus u v p q o)ᴴ * eq9BranchKraus u v p q o)ᴴ
            = (1 / 4 : ℂ) • ρ

end Qatlib.Concepts.QuditTeleport.ResourceIff
