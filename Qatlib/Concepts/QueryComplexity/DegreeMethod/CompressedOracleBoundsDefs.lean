/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.StoppingCore.InterruptBridge.BitToPhaseSameInput
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.CompressedQuery.CompressOracle

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Matrix

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

def databaseTargetHadamard :
    Matrix (((I × Bool) × W) × (I → Bool)) (((I × Bool) × W) × (I → Bool)) ℂ :=
  TensorGate controlHadamard 1

def databaseXorOracle (p : ℝ) :
    Matrix (((I × Bool) × W) × (I → Bool)) (((I × Bool) × W) × (I → Bool)) ℂ :=
  databaseTargetHadamard * compressedOracle p * databaseTargetHadamard

def databaseXorRun (p : ℝ) (C : Circuit ((I × Bool) × W))
    (ψ : QState ((I × Bool) × W)) : QState (((I × Bool) × W) × (I → Bool)) :=
  Run (databaseXorOracle p) (tensorLiftCircuit C) (TensorState ψ (Ket (fun _ => false)))

def decompressedXorRun (p : ℝ) (C : Circuit ((I × Bool) × W))
    (ψ : QState ((I × Bool) × W)) : QState (((I × Bool) × W) × (I → Bool)) :=
  ApplyGate (TensorGate (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ)
    (decompressGate p)) (databaseXorRun p C ψ)

def databaseXorMarginal (p : ℝ) (C : Circuit ((I × Bool) × W))
    (ψ : QState ((I × Bool) × W)) : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ :=
  fun q q' => ∑ d : I → Bool, databaseXorRun p C ψ (q, d) *
    star (databaseXorRun p C ψ (q', d))

def databaseHasRecords (k : ℕ) (d : I → Bool) : Prop := k ≤ databaseCard d

def databaseRecordsAt (j : I) (d : I → Bool) : Prop := d j = true

end Qatlib.Concepts.QueryComplexity.DegreeMethod
