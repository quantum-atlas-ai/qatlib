/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.BellReferenceProtocol
import Mathlib.Data.Fintype.Card

/-!
# Decoding collapsed Bell messages

`CollapsedMessageGuessing` formulates a decoding advantage for a noninjective but nonconstant
encoding of the four Bell outcomes. A decoder using the encoded message must recover the
original uniform outcome with probability strictly greater than one quarter. The communication
setting is teleportation [BennettEtAl1993Teleportation]; see also [Wilde2017] for the
information-theoretic background.

## Main statements

* `CollapsedMessageGuessing`: The proposition that every noninjective, nonconstant encoding of
  four Bell outcomes has a decoder with uniform outcome-recovery probability greater than `1 /
  4`.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
* [Wilde, 2017][Wilde2017]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.QuditTeleport.MessagingBounds

/-- The proposition that every noninjective, nonconstant encoding of four Bell outcomes has a
decoder with uniform outcome-recovery probability greater than `1 / 4`. -/
def CollapsedMessageGuessing : Prop :=
  ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (m : Bool × Bool → κ),
    ¬Function.Injective m → (∃ a b : Bool × Bool, m a ≠ m b) →
    ∃ g : κ → Bool × Bool,
      (1 / 4 : ℝ) < ((Finset.univ.filter (fun o => g (m o) = o)).card : ℝ) / 4

end Qatlib.Concepts.QuditTeleport.MessagingBounds
