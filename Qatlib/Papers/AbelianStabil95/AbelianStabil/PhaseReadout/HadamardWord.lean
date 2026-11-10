/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.HspRecovery.KitaevReadout.HadamardTestBitLawSubgoalQuan
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.HspRecovery.KitaevReadout
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Matrix
namespace Qatlib.Papers.AbelianStabil95.AbelianStabil.PhaseReadout

def hadamardQueryWord (I : Type) [Fintype I] [DecidableEq I] : Circuit (I × Bool) :=
  [.gate (TensorGate (1 : Matrix I I ℂ) Hadamard), .query,
   .gate (TensorGate (1 : Matrix I I ℂ) Hadamard)]

theorem hadamardQueryWord_run (I : Type) [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (ψ : QState (I × Bool)) :
    Run (eigenphaseControlledGate I U) (hadamardQueryWord I) ψ =
      ApplyGate (hadamardTestGate I U) ψ := by
  simp [hadamardQueryWord, Run, hadamardTestGate, applyGate_mul]

theorem hadamardQueryWord_counts (I : Type) [Fintype I] [DecidableEq I] :
    QueryCount (hadamardQueryWord I) = 1 ∧ GateCount (hadamardQueryWord I) = 2 := by
  simp [hadamardQueryWord, QueryCount, GateCount]

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
