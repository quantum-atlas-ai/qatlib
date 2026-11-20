/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CodingDecoding.CssRecovery.CssCircuit
public import QatlibTests.ParityCircuit

@[expose] public section

/-! # Joint X/Z syndrome extraction for a Bell stabilizer -/

namespace QatlibTests.CssCircuit

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
open Qatlib.Concepts.CodingDecoding.CssTesters.CssTester
open Qatlib.Concepts.CodingDecoding.CssRecovery
open QatlibTests.ParityCircuit (word firstGate flips propagated)

/-- The two-qubit Bell stabilizer has an XX check and a ZZ check. -/
def bell : CssData (Fin 2) (Fin 1) (Fin 1) where
  hX := circuitCheck word
  hZ := circuitCheck word
  hcompat := by decide +kernel

/-- The two actual two-CNOT rounds, with transversal Hadamards around the first, give the
joint Bell-state syndrome branch. -/
theorem bell_branch (η : Bits 1 × Bits 1) :
    (cssExtract word word).branch η =
      conjBranch (Matrix.reindexAlgEquiv ℂ ℂ (dataIndex 2) (cssSyndromeProjector bell η)) :=
  css_extract bell word word rfl rfl η

/-- The specified fault in the Hadamard-rotated round becomes a data phase flip and shifts
the measured X syndrome by one. The second parity round has no faults. -/
theorem bell_fault (η : Bits 1 × Bits 1) :
    readAfter (faultyOp word (fun _ => 0)) η.2 *
        (basisHad 2 * readAfter (faultyOp word (faultsAt word flips {firstGate})) η.1 * basisHad 2) =
      cssPauliZ (fun j : Fin 2 => if j = 1 then 1 else 0) *
        cssSyndromeProjector bell (η.1 - 1, η.2) := by
  have h := css_faultBranch bell word word rfl rfl (faultsAt word flips {firstGate}) (fun _ => 0) η
  have hz : faultRun word (fun _ => 0) 0 = 0 := by decide +kernel
  rw [propagated, hz] at h
  simpa using h

end QatlibTests.CssCircuit
