/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.QuditTeleportationProtocol
import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.QuditTeleport.DepolarizingLaw

open Matrix

def TeleportGuessingDepolarizing : Prop :=
  (∀ ρ : Operator 2,
    ∑ o : Bool × Bool, conjBranch (teleportBranchKraus o) ρ
      = ((Matrix.trace ρ) / 2 : ℂ) • (1 : Operator 2)) ∧
  (∀ (n : ℕ) [NeZero n] (ρ : Operator n),
    ∑ o : Fin n × Fin n, conjBranch (quditBranchKraus n o) ρ
      = ((Matrix.trace ρ) / (n : ℂ)) • (1 : Operator n))

end Qatlib.Concepts.QuditTeleport.DepolarizingLaw
