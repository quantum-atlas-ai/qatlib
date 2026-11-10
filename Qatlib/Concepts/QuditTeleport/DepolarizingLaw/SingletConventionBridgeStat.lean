/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.BellTeleportationInstrument
import Qatlib.Concepts.QuditTeleport.DepolarizingLaw.SingletConventionBridgeAuxiliary
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.QuditTeleport.DepolarizingLaw

open Matrix

def SingletConventionBridge : Prop :=
  (∀ o : Bool × Bool,
    singletBranchKraus o = singletSign o • teleportBranchKraus (singletSwap o)) ∧
  (∀ (ρ : Operator 2) (o : Bool × Bool),
    (singletCorrection o * singletBranchKraus o) * ρ *
      (singletCorrection o * singletBranchKraus o)ᴴ = (1 / 4 : ℂ) • ρ)

end Qatlib.Concepts.QuditTeleport.DepolarizingLaw
