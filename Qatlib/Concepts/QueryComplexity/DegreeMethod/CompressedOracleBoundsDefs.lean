/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.StoppingCore.InterruptBridge.BitToPhaseSameInput

/-!
# Compressed database bit oracle definitions

This module defines the database bit oracle `databaseXorOracle` by conjugating the compressed
phase oracle with a target Hadamard. This uses the standard bit and phase query conversion
described in [NielsenChuang2010].

The definitions package compressed execution from an empty database, decompression, the
algorithm marginal matrix, and predicates for the number and locations of database records.

## Main statements

* `databaseXorOracle`: the compressed oracle in the bit query basis.
* `databaseXorRun` and `decompressedXorRun`: compressed and decompressed executions.
* `databaseXorMarginal`: the algorithm marginal matrix.
* `databaseHasRecords` and `databaseRecordsAt`: database record predicates.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.CompressedQuery.CompressOracle

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Matrix

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

/-- The Hadamard gate on the Boolean response register, extended by the identity to the database
and other registers. -/
def databaseTargetHadamard :
    Matrix (((I × Bool) × W) × (I → Bool)) (((I × Bool) × W) × (I → Bool)) ℂ :=
  TensorGate controlHadamard 1

/-- The compressed database oracle conjugated by `databaseTargetHadamard` to implement a bit
query. -/
def databaseXorOracle (p : ℝ) :
    Matrix (((I × Bool) × W) × (I → Bool)) (((I × Bool) × W) × (I → Bool)) ℂ :=
  databaseTargetHadamard * compressedOracle p * databaseTargetHadamard

/-- Execution of a lifted circuit with the database bit oracle, starting from the algorithm
state and the all-false database basis state. -/
def databaseXorRun (p : ℝ) (C : Circuit ((I × Bool) × W))
    (ψ : QState ((I × Bool) × W)) : QState (((I × Bool) × W) × (I → Bool)) :=
  Run (databaseXorOracle p) (tensorLiftCircuit C) (TensorState ψ (Ket (fun _ => false)))

/-- The compressed database execution followed by `decompressGate p` on the database register. -/
def decompressedXorRun (p : ℝ) (C : Circuit ((I × Bool) × W))
    (ψ : QState ((I × Bool) × W)) : QState (((I × Bool) × W) × (I → Bool)) :=
  ApplyGate (TensorGate (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ)
    (decompressGate p)) (databaseXorRun p C ψ)

/-- The algorithm marginal matrix obtained by summing compressed joint amplitude outer products
over the database register. -/
def databaseXorMarginal (p : ℝ) (C : Circuit ((I × Bool) × W))
    (ψ : QState ((I × Bool) × W)) : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ :=
  fun q q' => ∑ d : I → Bool, databaseXorRun p C ψ (q, d) *
    star (databaseXorRun p C ψ (q', d))

/-- The condition that the database record count is at least `k`. -/
def databaseHasRecords (k : ℕ) (d : I → Bool) : Prop := k ≤ databaseCard d

/-- The condition that the Boolean database has a record at address `j`. -/
def databaseRecordsAt (j : I) (d : I → Bool) : Prop := d j = true

end Qatlib.Concepts.QueryComplexity.DegreeMethod
