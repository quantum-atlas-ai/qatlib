/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Concepts.MixedInstrument.RewindAlgebra.RejectionFailureBoundDefs
open Qatlib.Foundations.PureStateMath
open Qatlib

namespace Qatlib.Concepts.MixedInstrument.RewindAlgebra

open Matrix

variable {D : ℕ}

def RejectionFailureBound : Prop :=
  ∀ (D : ℕ) (P Q : Operator D), P.IsHermitian → P * P = P → Q.IsHermitian → Q * Q = Q →
    ∀ ψ : QState (Fin D), Inner ψ ψ = 1 → P *ᵥ ψ = ψ →
      ∀ n : ℕ, 1 ≤ n → rejectFailProb P Q ψ n ≤ 1 / (2 * (n + 1))

end Qatlib.Concepts.MixedInstrument.RewindAlgebra
