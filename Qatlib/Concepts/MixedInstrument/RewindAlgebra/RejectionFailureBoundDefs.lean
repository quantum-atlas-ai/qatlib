/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.MixedState

/-!
# Rejection rounds and failure probability

This module defines the operator products underlying rejection rewinding. `rejectRound`
compresses a chosen measurement branch to the complement of the first projector, `rejectWord`
composes a Boolean history of rounds, and `rejectFailProb` sums the resulting squared norms
after the initial failed measurements. These expressions model the rejection analysis of
[TemmeEtAl2011].

## Main statements

* `rejectRound`: The operator `(1 - P) * (if s then Q else 1 - Q) * (1 - P)` for one selected
  rejection round.
* `rejectWord`: The ordered product of `n` rejection round operators along the Boolean history
  `s`, with identity for the empty history.
* `rejectFailProb`: The sum over Boolean histories of the real squared norms after applying the
  rejection word to `(1 - P) *ᵥ ((1 - Q) *ᵥ ψ)`.

## References

* [Temme et al., 2011][TemmeEtAl2011]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib

open Matrix

variable {D : ℕ}

namespace Qatlib.Concepts.MixedInstrument.RewindAlgebra

/-- The operator `(1 - P) * (if s then Q else 1 - Q) * (1 - P)` for one selected rejection
round. -/
noncomputable def rejectRound (P Q : Operator D) (s : Bool) : Operator D :=
  (1 - P) * (if s then Q else 1 - Q) * (1 - P)

/-- The ordered product of `n` rejection round operators along the Boolean history `s`, with
identity for the empty history. -/
noncomputable def rejectWord (P Q : Operator D) (n : ℕ) (s : Fin n → Bool) : Operator D :=
  Fin.foldr n (fun j acc => rejectRound P Q (s j) * acc) 1

/-- The sum over Boolean histories of the real squared norms after applying the rejection word
to `(1 - P) *ᵥ ((1 - Q) *ᵥ ψ)`. -/
noncomputable def rejectFailProb (P Q : Operator D) (ψ : QState (Fin D)) (n : ℕ) : ℝ :=
  ∑ s : Fin n → Bool,
    (Inner (rejectWord P Q n s *ᵥ ((1 - P) *ᵥ ((1 - Q) *ᵥ ψ)))
      (rejectWord P Q n s *ᵥ ((1 - P) *ᵥ ((1 - Q) *ᵥ ψ)))).re
end Qatlib.Concepts.MixedInstrument.RewindAlgebra
