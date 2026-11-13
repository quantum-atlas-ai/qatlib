/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.KitaevReadout.EigenphaseHadamardTest

/-!
# Specification of the Hadamard test bit law

`HadamardTestBitLawSubgoal` states the tensor-product output identity for a Hadamard test on an
eigenvector and the associated ancilla Born probabilities. The cosine bit law is the basic phase
readout primitive in [Kitaev1995].

## Main statements

* `HadamardTestBitLawSubgoal`: the eigenvector output identity and both ancilla probabilities.

## References

* [Kitaev, 1995][Kitaev1995]
-/

open Matrix
open scoped Classical

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.HspRecovery.KitaevReadout

/-- Specifies the Hadamard test output on an eigenvector as its tensor product with the
phase-dependent ancilla state, together with both cosine-dependent Born probabilities. -/
def HadamardTestBitLawSubgoal : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (U : Matrix I I ℂ) (ψ : QState I) (φ : ℝ),
    (U *ᵥ ψ = eigenPhase φ • ψ) →
    ApplyGate (hadamardTestGate I U) (TensorState ψ (Ket false))
      = TensorState ψ (hadamardTestBitState (eigenPhase φ))
    ∧ BornProb (hadamardTestBitState (eigenPhase φ)) false
        = (1 + Real.cos (2 * Real.pi * φ)) / 2
    ∧ BornProb (hadamardTestBitState (eigenPhase φ)) true
        = (1 - Real.cos (2 * Real.pi * φ)) / 2

end Qatlib.Concepts.HspRecovery.KitaevReadout
