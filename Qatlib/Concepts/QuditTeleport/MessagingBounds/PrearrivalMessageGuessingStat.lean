/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.BellReferenceProtocol
import Mathlib.Data.Fintype.Card
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.QuditTeleport.MessagingBounds

def PrearrivalMessageGuessing : Prop :=
  ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (m : Bool × Bool → κ),
    ¬Function.Injective m →
    ∃ guess : κ,
      (1 / 2 : ℝ) ≤ ((Finset.univ.filter (fun o => m o = guess)).card : ℝ) / 4 ∧
      (1 / 4 : ℝ) < ((Finset.univ.filter (fun o => m o = guess)).card : ℝ) / 4

end Qatlib.Concepts.QuditTeleport.MessagingBounds
