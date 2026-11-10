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

def CollapsedMessageGuessing : Prop :=
  ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (m : Bool × Bool → κ),
    ¬Function.Injective m → (∃ a b : Bool × Bool, m a ≠ m b) →
    ∃ g : κ → Bool × Bool,
      (1 / 4 : ℝ) < ((Finset.univ.filter (fun o => g (m o) = o)).card : ℝ) / 4

end Qatlib.Concepts.QuditTeleport.MessagingBounds
