/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.ResourceIff.Eq9Aux
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QuditTeleport.ResourceIff

open Matrix

def Eq9ResourceTeleportation : Prop :=
  ∀ (u v p q : QState Bool), eq9OrthoPairsB u v p q →
    ∀ o : Bool × Bool,
      (((2 : ℂ) • (eq9BranchKraus u v p q o)ᴴ) ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧
      ∀ ρ : Operator 2,
        ((2 : ℂ) • (eq9BranchKraus u v p q o)ᴴ * eq9BranchKraus u v p q o) * ρ *
          ((2 : ℂ) • (eq9BranchKraus u v p q o)ᴴ * eq9BranchKraus u v p q o)ᴴ
            = (1 / 4 : ℂ) • ρ

end Qatlib.Concepts.QuditTeleport.ResourceIff
