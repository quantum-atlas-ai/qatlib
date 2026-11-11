/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.Transform

/-!
# Specification of Fourier support uncertainty

`FourierSupportUncertainty` records the support-product lower bound for the cyclic quantum
Fourier transform `zmodQFT`. Both supports consist of coordinates with nonzero amplitude. For
background, see [Cornwell2014].

## Main statements

* `FourierSupportUncertainty`: The proposition that `N` is at most the product of the support
  sizes of any nonzero state on `ZMod N` and its quantum Fourier transform.

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option warningAsError false
set_option autoImplicit false
open scoped Classical
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.AbelianDecoders.FourierSupport

/-- The proposition that `N` is at most the product of the support sizes of any nonzero state on
`ZMod N` and its quantum Fourier transform. -/
def FourierSupportUncertainty : Prop :=
  ∀ (N : ℕ) [NeZero N] (ψ : QState (ZMod N)), ψ ≠ 0 →
    N ≤ (Finset.univ.filter (fun x => ψ x ≠ 0)).card *
      (Finset.univ.filter (fun y => zmodQFT ψ y ≠ 0)).card
end Qatlib.Concepts.AbelianDecoders.FourierSupport
