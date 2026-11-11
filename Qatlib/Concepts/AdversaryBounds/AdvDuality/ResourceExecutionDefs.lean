/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.ResourceBoundsTransport
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.FreshCopyExecution

/-!
# Definitions for execution resource accounting

This module defines the data used to compare resource accounts with executed instruction words.
`UnifiedCounts` records forward queries, adjoint queries, and Hamiltonian evolutions; `Program`
packages a word, its initial live-wire count, and a readout of the final live wires. `shiftWord`
and `mergeWords` provide wire renaming for composition, while `freshRunAccount` extracts an
account from a fresh-copy execution. Quantum circuits and their resource counts have the
standard background described in [NielsenChuang2010].

The remaining definitions supply concrete instruction words for gate emission, LCU terms, and
stopping costs, together with `CertifiedSynthesis` and `compileErrorBudget` for recording
synthesis data and reference-error bounds.

## Main statements

* `UnifiedCounts`: forward-query, adjoint-query, and evolution counts.
* `Program`: instruction words with a readout and an execution account.
* `CertifiedSynthesis`: certificate data with a reference-error bound.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010], *Quantum Computation and Quantum Information*.
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib
open Qatlib
open Qatlib
open Qatlib
open scoped ENNReal

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

/-- The forward-query, adjoint-query, and Hamiltonian-evolution counts of an execution. -/
structure UnifiedCounts where

  queryCount : ℕ

  adjointQueryCount : ℕ

  hamiltonianCount : ℕ
  deriving DecidableEq, Repr

/-- Extract the forward-query, adjoint-query, and Hamiltonian-evolution counts from a resource
account. -/
def UnifiedCounts.ofAccount (a : Account) : UnifiedCounts :=
  ⟨a.queries, a.adjointQueries, a.hamiltonianCount⟩

/-- The sum of the forward-query and adjoint-query counts. -/
def UnifiedCounts.total (c : UnifiedCounts) : ℕ := c.queryCount + c.adjointQueryCount

/-- The indicator that an instruction is a forward oracle call. -/
def forwardOracleStep : DynStep → ℕ
  | .oracle false _ => 1
  | .oracle true _ => 0
  | .macro _ => 0
  | .evolve _ => 0
  | .classical _ => 0
  | .alloc _ => 0
  | .releaseClean _ => 0
  | .releaseDirty _ => 0
  | .reset _ => 0
  | .uncompute _ => 0

/-- The indicator that an instruction is an adjoint oracle call. -/
def adjointOracleStep : DynStep → ℕ
  | .oracle false _ => 0
  | .oracle true _ => 1
  | .macro _ => 0
  | .evolve _ => 0
  | .classical _ => 0
  | .alloc _ => 0
  | .releaseClean _ => 0
  | .releaseDirty _ => 0
  | .reset _ => 0
  | .uncompute _ => 0

/-- The indicator that an instruction is a Hamiltonian-evolution step. -/
def evolveStep : DynStep → ℕ
  | .oracle false _ => 0
  | .oracle true _ => 0
  | .macro _ => 0
  | .evolve _ => 1
  | .classical _ => 0
  | .alloc _ => 0
  | .releaseClean _ => 0
  | .releaseDirty _ => 0
  | .reset _ => 0
  | .uncompute _ => 0

/-- Count the forward oracle calls in an instruction word. -/
def forwardOracleCount : List DynStep → ℕ
  | [] => 0
  | s :: rest => forwardOracleStep s + forwardOracleCount rest

/-- Count the adjoint oracle calls in an instruction word. -/
def adjointOracleCount : List DynStep → ℕ
  | [] => 0
  | s :: rest => adjointOracleStep s + adjointOracleCount rest

/-- Count the Hamiltonian-evolution steps in an instruction word. -/
def evolveCount : List DynStep → ℕ
  | [] => 0
  | s :: rest => evolveStep s + evolveCount rest

/-- Convert the cost returned by running fresh-copy operations from `X` into a resource account. -/
noncomputable def freshRunAccount {n M : ℕ} (ops : List (Qatlib.Concepts.FreshCopyExec.QpeConsumers.Op n M))
    (X : Qatlib.Concepts.FreshCopyExec.QpeConsumers.State n M) : Account :=
  Account.ofFreshCost ((Qatlib.Concepts.FreshCopyExec.QpeConsumers.run ops X).2)

/-- The cost returned by running a list of fresh-copy operations from the initial state `X`. -/
noncomputable def freshRunCost {n M : ℕ} (ops : List (Qatlib.Concepts.FreshCopyExec.QpeConsumers.Op n M))
    (X : Qatlib.Concepts.FreshCopyExec.QpeConsumers.State n M) : Qatlib.Concepts.FreshCopyExec.QpeConsumers.Cost :=
  (Qatlib.Concepts.FreshCopyExec.QpeConsumers.run ops X).2

/-- Increase each explicit wire index in an allocation, release, reset, or uncomputation
instruction by `k`. Other instructions are preserved. -/
def shiftStepWires (k : ℕ) : DynStep → DynStep
  | .alloc w => .alloc (w + k)
  | .releaseClean w => .releaseClean (w + k)
  | .releaseDirty w => .releaseDirty (w + k)
  | .reset w => .reset (w + k)
  | .uncompute w => .uncompute (w + k)
  | s => s

/-- Apply `shiftStepWires k` to every instruction in a word. -/
def shiftWord (k : ℕ) : List DynStep → List DynStep := List.map (shiftStepWires k)

/-- One more than the explicit wire index of an allocation, release, reset, or uncomputation
instruction, and zero for other instructions. -/
def stepTouchedWire : DynStep → ℕ
  | .alloc w | .releaseClean w | .releaseDirty w | .reset w | .uncompute w => w + 1
  | _ => 0

/-- The maximum value of `stepTouchedWire` over an instruction word, with value zero for the
empty word. -/
def wordWireBound : List DynStep → ℕ :=
  List.foldl (fun acc s => max acc (stepTouchedWire s)) 0

/-- Append `b` to `a` after shifting its explicit wire indices by `wordWireBound a`. -/
def mergeWords (a b : List DynStep) : List DynStep :=
  a ++ shiftWord (wordWireBound a) b

/-- An instruction word with an initial live-wire count and an output function on the final list
of live wires. -/
structure Program (Out : Type*) where

  word : List DynStep

  base : ℕ

  readout : List ℕ → Out

/-- The resource account of a program's instruction word with its specified initial live-wire
count. -/
def Program.account {Out : Type*} (P : Program Out) : Account :=
  Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs.account P.base P.word

/-- The completed outcome containing the program's readout of its final live wires and its
resource account. -/
def Program.outcome {Out : Type*} (P : Program Out) : Outcome (Out × Account) :=
  .done (P.readout (finalLive P.base P.word), P.account)

/-- View a program as a generator that returns `Program.outcome` for every instance. -/
def Program.gen {Out : Type*} {Inst : Type*} (P : Program Out) : Gen Inst Out :=
  fun _ => P.outcome

/-- The product of the size and precision filters on pairs of size and precision parameters. -/
def jointFilter : Filter (ℕ × ℝ) := sizeFilter ×ˢ precFilter

/-- The gate budget given by the length of the synthesis certificate at precision parameter `E`.
The size argument of the resulting budget is unused. -/
def certifiedGateBudget (n : ℕ) (cert : ℝ → SynthCertificate n) : GateBudget :=
  fun _ E => (cert E).word.length

/-- Replace each gate code by a classical step charged `bits` followed by the corresponding
macro instruction. -/
def machineWord (bits : ℕ) (word : List FiniteGateCode) : List DynStep :=
  word.flatMap (fun g => [DynStep.classical bits, DynStep.macro g])

/-- The classical-bit charge in the resource account of `machineWord bits word`, starting with
no live wires. -/
def emissionTime (bits : ℕ) (word : List FiniteGateCode) : ℕ :=
  (account 0 (machineWord bits word)).classicalBits

/-- The instruction word that allocates wire zero, executes a macro, and releases that wire
cleanly for each LCU term code. -/
def lcuTermProgram (terms : List FiniteGateCode) : List DynStep :=
  terms.flatMap (fun g => [DynStep.alloc 0, DynStep.macro g, DynStep.releaseClean 0])

/-- The number of gate codes in a list of LCU terms. -/
def lcuTermCount (terms : List FiniteGateCode) : ℕ := terms.length

/-- The three-instruction block that allocates wire zero, executes macro `g`, and releases wire
zero cleanly. -/
def lcuTermBlock (g : FiniteGateCode) : List DynStep :=
  [DynStep.alloc 0, DynStep.macro g, DynStep.releaseClean 0]

/-- A two-step classical instruction word recording preparation and trial charges. -/
def stoppingWord (prep trial : ℕ) : List DynStep :=
  [DynStep.classical prep, DynStep.classical trial]

/-- Translate a circuit query into a forward oracle instruction and a circuit gate into a fixed
Hadamard macro for resource counting. -/
def circuitResourceStep {I : Type} (s : Step I) : DynStep :=
  match s with
  | .query => DynStep.oracle false []
  | .gate _ => DynStep.macro (.h 0)

/-- Translate a circuit into resource instructions between allocation and clean release of the
wire `work`. -/
def circuitResourceWord {I : Type} (C : Circuit I) (work : ℕ) : List DynStep :=
  DynStep.alloc work :: (C.map circuitResourceStep ++ [DynStep.releaseClean work])

/-- A synthesis certificate together with ideal and actual matrices and a nonnegative error
satisfying `RefBounded actual ideal error`. -/
structure CertifiedSynthesis (n d : ℕ) where

  cert : SynthCertificate n

  ideal : Matrix (Fin d) (Fin d) ℂ

  actual : Matrix (Fin d) (Fin d) ℂ

  error : ℝ

  error_nonneg : 0 ≤ error

  ref_bounded : RefBounded actual ideal error

/-- The reciprocal error budget `1 / E` as a real-valued function of the precision parameter. -/
noncomputable def compileErrorBudget (E : ℝ) : ℝ := 1 / E

end Qatlib.Concepts.AdversaryBounds.AdvDuality
