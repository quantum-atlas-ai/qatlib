/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CodingDecoding.CssRecovery.ParityCircuit
import Mathlib.Data.Fintype.Powerset

@[expose] public section

/-! # Executed parity check and one propagated gate fault -/

namespace QatlibTests.ParityCircuit

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CodingDecoding.CssRecovery
open scoped Matrix

/-- Two explicit CNOTs compute the equality check of a two-qubit repetition code. -/
def word : List (ParityGate 2 1) := [⟨0, 0⟩, ⟨1, 0⟩]

/-- The actual circuit defines the Z check matrix of the example. -/
def code : CssData (Fin 2) (Fin 0) (Fin 1) where
  hX := 0
  hZ := circuitCheck word
  hcompat := by funext i; exact Fin.elim0 i

/-- The first location of this particular two-gate word. -/
def firstGate : Fin word.length := ⟨0, by decide +kernel⟩

/-- The prescribed fault at the first gate flips the second data qubit. -/
def flips (i : Fin word.length) : Joint 2 1 :=
  if i = firstGate then (fun j => if j = 1 then 1 else 0, 0) else 0

/-- The second CNOT propagates the fault into the ancillary syndrome. -/
theorem propagated :
    faultRun word (faultsAt word flips {firstGate}) 0 = (fun j => if j = 1 then 1 else 0, 1) := by
  decide +kernel

/-- Preparing and measuring the actual circuit gives the same branch as projecting onto the
syndrome of its Z-check matrix. -/
theorem ideal_branch (η : Bits 1) :
    readAfter (parityOp word) η =
      Matrix.diagonal (fun x : Bits 2 => if code.hZ *ᵥ x = η then (1 : ℂ) else 0) :=
  parity_branch word η

/-- The branch of the actual circuit instrument consumes the checked Kraus operator. -/
theorem ideal_instrument (η : Bits 1) (ρ : Operator (Fintype.card (Bits 2))) :
    (parityInstr word).branch η ρ = parityKraus word η * ρ * (parityKraus word η)ᴴ :=
  parity_outcome word η ρ

/-- With zero input and a fault after the first CNOT, the sole surviving ancilla outcome is
one and the surviving data label has its second bit flipped. -/
theorem noisy_outcome :
    readAfter (faultyOp word (faultsAt word flips {firstGate})) (1 : Bits 1)
      (fun j => if j = 1 then 1 else 0) 0 = 1 := by
  rw [faulty_branch, propagated]
  simp

/-- The actual propagated residual of every single-location fault has weight at most one. -/
theorem gadget_tolerant : (parityGadget code word flips).IsFaultTolerantAt 1 := by
  apply gadget_bound
  decide +kernel

/-- The example decoder flips the second data bit when the CNOT readout reports odd parity. -/
def decoder : RecoveryProgram code where
  corr η := (fun j => if j = 1 then η.2 0 else 0, 0)
  decodeTime := fun _ => 1

/-- The observed syndrome repairs the actual propagated first-location fault. -/
theorem noisy_decoded :
    residualFromObserved decoder ((faultRun word (faultsAt word flips {firstGate}) 0).1, 0)
      (0, (faultRun word (faultsAt word flips {firstGate}) 0).2) = 0 := by
  rw [propagated]
  decide +kernel

end QatlibTests.ParityCircuit
