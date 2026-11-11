/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.Transform

/-!
# Specification of cyclic Fourier nonvanishing

`NoConsecutiveFourierZeros` states the cyclic-window nonvanishing property for `zmodQFT`.
Starting at any residue, a nonzero Fourier coefficient occurs within as many consecutive
positions as the original support size. For background, see [Cornwell2014].

## Main statements

* `NoConsecutiveFourierZeros`: The proposition that every cyclic window of length equal to the
  support size of a nonzero state contains a nonzero Fourier coefficient.

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option warningAsError false
set_option autoImplicit false
open scoped Classical
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.AbelianDecoders.FourierSupport

/-- The proposition that every cyclic window of length equal to the support size of a nonzero
state contains a nonzero Fourier coefficient. -/
def NoConsecutiveFourierZeros : Prop :=
  ∀ (N : ℕ) [NeZero N] (ψ : QState (ZMod N)), ψ ≠ 0 →
    ∀ a : ZMod N, ∃ t : Fin ((Finset.univ.filter (fun x => ψ x ≠ 0)).card),
      zmodQFT ψ (a + (t.val : ZMod N)) ≠ 0
end Qatlib.Concepts.AbelianDecoders.FourierSupport
