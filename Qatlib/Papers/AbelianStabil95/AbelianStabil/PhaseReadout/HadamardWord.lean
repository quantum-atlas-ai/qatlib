/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.HspRecovery.KitaevReadout.HadamardTestBitLawSubgoalQuan

/-!
# A circuit word for the Hadamard test

`hadamardQueryWord` represents the Hadamard–query–Hadamard sequence on a data register and one
control bit. Its execution agrees with `hadamardTestGate`, and the module computes both its
operation counts and its eigenstate output amplitudes through the resulting Born probabilities.
The development follows [Kitaev1995].

## Main statements

* `hadamardQueryWord_run`: identifies the circuit execution with the Hadamard-test matrix.
* `hadamardQueryWord_eigenstate`: gives the product output state and cosine probabilities.

## References

* [Kitaev, 1995][Kitaev1995]
-/

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.HspRecovery.KitaevReadout
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Matrix
namespace Qatlib.Papers.AbelianStabil95.AbelianStabil.PhaseReadout

/-- The circuit consisting of a Hadamard gate on the control bit, one query, and a second
control Hadamard gate. -/
def hadamardQueryWord (I : Type) [Fintype I] [DecidableEq I] : Circuit (I × Bool) :=
  [.gate (TensorGate (1 : Matrix I I ℂ) Hadamard), .query,
   .gate (TensorGate (1 : Matrix I I ℂ) Hadamard)]

/-- Executing the Hadamard query word with the eigenphase-controlled gate equals applying the
Hadamard-test gate, as used in [Kitaev, 1995, Lemma 9][Kitaev1995]. -/
theorem hadamardQueryWord_run (I : Type) [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (ψ : QState (I × Bool)) :
    Run (eigenphaseControlledGate I U) (hadamardQueryWord I) ψ =
      ApplyGate (hadamardTestGate I U) ψ := by
  simp [hadamardQueryWord, Run, hadamardTestGate, applyGate_mul]

/-- The Hadamard query word uses one query and two ordinary gates, as used in [Kitaev, 1995,
Lemma 9][Kitaev1995]. -/
theorem hadamardQueryWord_counts (I : Type) [Fintype I] [DecidableEq I] :
    QueryCount (hadamardQueryWord I) = 1 ∧ GateCount (hadamardQueryWord I) = 2 := by
  simp [hadamardQueryWord, QueryCount, GateCount]

/-- On an eigenvector with phase `φ` and a zero control bit, the query word preserves the data
factor and produces control probabilities `(1 ± cos (2 * π * φ)) / 2`. This is the
elementary sampling step for [Kitaev, 1995, Lemma 9][Kitaev1995]. -/
theorem hadamardQueryWord_eigenstate (I : Type) [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (ψ : QState I) (φ : ℝ)
    (hU : U *ᵥ ψ = eigenPhase φ • ψ) :
    Run (eigenphaseControlledGate I U) (hadamardQueryWord I)
        (TensorState ψ (Ket false)) =
      TensorState ψ (hadamardTestBitState (eigenPhase φ)) ∧
    BornProb (hadamardTestBitState (eigenPhase φ)) false =
      (1 + Real.cos (2 * Real.pi * φ)) / 2 ∧
    BornProb (hadamardTestBitState (eigenPhase φ)) true =
      (1 - Real.cos (2 * Real.pi * φ)) / 2 := by
  rw [hadamardQueryWord_run]
  exact hadamardTestBitLawSubgoal I U ψ φ hU

end Qatlib.Papers.AbelianStabil95.AbelianStabil.PhaseReadout
