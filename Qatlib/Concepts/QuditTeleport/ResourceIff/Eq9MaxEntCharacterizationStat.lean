/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.ResourceIff.Eq9Aux
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QuditTeleport.ResourceIff

def Eq9MaxEntCharacterization : Prop :=
  ∀ (Ψ : QState (Fin 2 × Fin 2)), Normalized Ψ →
    PartialTrace (outerProduct Ψ) = (1 / 2 : ℂ) • (1 : Operator 2) →
    ∃ u v p q : QState (Fin 2), eq9OrthoPairs u v p q ∧ eq9Resource u v p q = Ψ

end Qatlib.Concepts.QuditTeleport.ResourceIff
