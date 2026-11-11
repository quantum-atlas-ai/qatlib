/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Concepts.MixedInstrument.RewindAlgebra.RejectionFailureBoundDefs

/-!
# Rejection failure bound specification

`RejectionFailureBound` specifies the inverse linear bound on the failure probability of
repeated rejection measurements. Its hypotheses require two Hermitian projectors and a
normalized state in the range of the first, and its round count is at least one. The estimate
belongs to the quantum Metropolis rejection analysis [TemmeEtAl2011].

## Main statements

* `RejectionFailureBound`: The proposition that rejection failure for two orthogonal projectors
  and a normalized input fixed by the first is at most `1 / (2 * (n + 1))` for `n ≥ 1`.

## References

* [Temme et al., 2011][TemmeEtAl2011]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib

namespace Qatlib.Concepts.MixedInstrument.RewindAlgebra

open Matrix

variable {D : ℕ}

/-- The proposition that rejection failure for two orthogonal projectors and a normalized input
fixed by the first is at most `1 / (2 * (n + 1))` for `n ≥ 1`. -/
def RejectionFailureBound : Prop :=
  ∀ (D : ℕ) (P Q : Operator D), P.IsHermitian → P * P = P → Q.IsHermitian → Q * Q = Q →
    ∀ ψ : QState (Fin D), Inner ψ ψ = 1 → P *ᵥ ψ = ψ →
      ∀ n : ℕ, 1 ≤ n → rejectFailProb P Q ψ n ≤ 1 / (2 * (n + 1))

end Qatlib.Concepts.MixedInstrument.RewindAlgebra
