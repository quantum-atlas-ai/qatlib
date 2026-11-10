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
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.QuditTeleport.ResourceIff

namespace Qatlib.Concepts.QuditTeleport.QdLoccModel

def Eq9MaxEntMarginals : Prop :=
  ∀ (u v p q : QState (Fin 2)), eq9OrthoPairs u v p q →
    PartialTrace (outerProduct (eq9Resource u v p q)) = (1 / 2 : ℂ) • (1 : Operator 2) ∧
    PartialTrace (relabelGate (Equiv.prodComm (Fin 2) (Fin 2))
      (outerProduct (eq9Resource u v p q))) = (1 / 2 : ℂ) • (1 : Operator 2)

end Qatlib.Concepts.QuditTeleport.QdLoccModel
