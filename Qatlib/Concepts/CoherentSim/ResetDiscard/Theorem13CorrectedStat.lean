/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.LinearCombination
import Qatlib.Concepts.CoherentSim.ResetDiscard.Theorem13Figure3Defs

/-!
# Statement of the LCU success bound

`Theorem13Corrected` specifies a success-probability bound for an LCU circuit with unitary
branches and ancillary gates satisfying a coefficient factorization. The bound uses the norm of
the weighted branch output and the total coefficient norm, in the setting of [ChildsWiebe2012].

## Main statements

* `Theorem13Corrected`: The proposition specifying the coefficient-mass success bound.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

set_option warningAsError false
open Qatlib.Foundations.PureStateMath

open Matrix

namespace Qatlib.Concepts.CoherentSim.ResetDiscard

/-- The proposition that the selected-fiber success probability of the stated LCU circuit on
normalized inputs is at most the squared weighted-output norm divided by `(∑ m, ‖C m‖)²`,
assuming the unitary and coefficient-factorization conditions. -/
def Theorem13Corrected : Prop :=
  ∀ (J I : Type) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (U : J → Matrix I I ℂ), (∀ m, U m ∈ Matrix.unitaryGroup I ℂ) →
    ∀ (C : J → ℂ), 0 < ∑ m, ‖C m‖ →
    ∀ (A : Matrix J J ℂ), A ∈ Matrix.unitaryGroup J ℂ →
    ∀ (B : Matrix J J ℂ), B ∈ Matrix.unitaryGroup J ℂ →
    ∀ (j₀ : J) (K : ℂ), (∀ m, B j₀ m * A m j₀ = K * C m) →
    ∀ ψ : QState I, Normalized ψ →
      Fig3SuccessProb U A B j₀ ψ
        ≤ (∑ i, ‖((∑ m, C m • U m) *ᵥ ψ) i‖ ^ 2) / (∑ m, ‖C m‖) ^ 2

end Qatlib.Concepts.CoherentSim.ResetDiscard
