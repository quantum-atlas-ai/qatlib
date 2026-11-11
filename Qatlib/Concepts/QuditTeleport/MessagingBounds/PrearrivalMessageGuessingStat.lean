/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.BellReferenceProtocol
import Mathlib.Data.Fintype.Card

/-!
# Guessing a Bell message before arrival

`PrearrivalMessageGuessing` states that a noninjective encoding of four uniform Bell outcomes
has a message value of probability at least one half. This is a bound for guessing the encoded
message before observing it. The communication setting is teleportation
[BennettEtAl1993Teleportation]; see also [Wilde2017] for the information-theoretic background.

## Main statements

* `PrearrivalMessageGuessing`: The proposition that every noninjective Bell-outcome encoding has
  a message value with probability at least `1 / 2`, and hence strictly greater than `1 / 4`.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
* [Wilde, 2017][Wilde2017]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.QuditTeleport.MessagingBounds

/-- The proposition that every noninjective Bell-outcome encoding has a message value with
probability at least `1 / 2`, and hence strictly greater than `1 / 4`. -/
def PrearrivalMessageGuessing : Prop :=
  ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (m : Bool × Bool → κ),
    ¬Function.Injective m →
    ∃ guess : κ,
      (1 / 2 : ℝ) ≤ ((Finset.univ.filter (fun o => m o = guess)).card : ℝ) / 4 ∧
      (1 / 4 : ℝ) < ((Finset.univ.filter (fun o => m o = guess)).card : ℝ) / 4

end Qatlib.Concepts.QuditTeleport.MessagingBounds
