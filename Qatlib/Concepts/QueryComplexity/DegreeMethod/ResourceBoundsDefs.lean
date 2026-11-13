/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.ResourceDerivation
import Qatlib.Concepts.CoherentSim.CoherentOAA.QueryCircuit
import Qatlib.Foundations.QueryWordCore.HamiltonianQuery
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.CopyDrivenPhaseReadout
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.LocalCopyQPEConsumers
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.NumericalCopyQPE
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.TwoSpeciesCopyPhaseReadout
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.FreshCopyComposition
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.CopyPureReadout
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.CopySpectralReadout

/-!
# Resource ledgers and local allocation

This module assigns resource costs to adjoint query words and Hamiltonian-query programs,
and adapts fresh-copy resource tuples to `FreshCopyLedger`. The circuit and evolution
viewpoints are standard in [NielsenChuang2010].

It also defines budgeted implementation, query lower bounds, one-sided asymptotic
resource comparisons, and a stack-based local allocation model with peak-space tracking.

## Main statements

* `adjointWordResourceCost_queries`: the query ledger counts forward and backward access.
* `hamiltonianProgramResourceCost_hamiltonianTime`: the time ledger equals total absolute
  evolution time under zero-time gate profiles.
* `ImplementsWithBudget`: approximation, unitarity, and a componentwise cost budget.
* `localPeakSpace`: maximum live allocation in a local program.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
* [Cleve et al., 2009][CleveEtAl2009]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Foundations.QueryWordCore.HamiltonianQuery

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Matrix
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open Qatlib.Concepts.CoherentSim.CoherentOAA (AdjointStep adjointQueryCount adjointGateCount)

set_option autoImplicit false

instance instLEResourceCost : LE ResourceCost where
  le a b := a.queries ≤ b.queries ∧ a.macroGates ≤ b.macroGates ∧
    a.basicGates ≤ b.basicGates ∧ a.depth ≤ b.depth ∧ a.peakSpace ≤ b.peakSpace ∧
    a.hamiltonianTime ≤ b.hamiltonianTime ∧ a.classicalBits ≤ b.classicalBits

/-- Componentwise comparison of resource costs is reflexive. -/
theorem le_refl (a : ResourceCost) : a ≤ a :=
  ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩

/-- Accumulate macro-gate profiles and oracle-step charges along an adjoint word, charging both
forward and backward access. -/
def adjointWordResourceCost {H : Type*} (κg : Matrix H H ℂ → StepProfile) :
    List (AdjointStep H) → ResourceCost
  | [] => 0
  | .gate V :: W => ResourceCost.ofMacroStep (κg V) + adjointWordResourceCost κg W
  | .forward :: W => ResourceCost.ofOracleStep + adjointWordResourceCost κg W
  | .backward :: W => ResourceCost.ofOracleStep + adjointWordResourceCost κg W

/-- The query component of an adjoint word's resource cost equals its adjoint query count. -/
@[simp] theorem adjointWordResourceCost_queries {H : Type*}
    (κg : Matrix H H ℂ → StepProfile) (W : List (AdjointStep H)) :
    (adjointWordResourceCost κg W).queries = adjointQueryCount W := by
  induction W with
  | nil => rfl
  | cons s W ih =>
    cases s with
    | gate V => simp [adjointWordResourceCost, adjointQueryCount, ih]
    | forward => simp [adjointWordResourceCost, adjointQueryCount, ih, Nat.add_comm]
    | backward => simp [adjointWordResourceCost, adjointQueryCount, ih, Nat.add_comm]

/-- The macro-gate component of an adjoint word's resource cost equals its adjoint gate count. -/
@[simp] theorem adjointWordResourceCost_macroGates {H : Type*}
    (κg : Matrix H H ℂ → StepProfile) (W : List (AdjointStep H)) :
    (adjointWordResourceCost κg W).macroGates = adjointGateCount W := by
  induction W with
  | nil => rfl
  | cons s W ih =>
    cases s with
    | gate V => simp [adjointWordResourceCost, adjointGateCount, ih, Nat.add_comm]
    | forward => simp [adjointWordResourceCost, adjointGateCount, ih]
    | backward => simp [adjointWordResourceCost, adjointGateCount, ih]

/-- The resource cost charging only Hamiltonian time, by the nonnegative extended-real value of
`|t|`. -/
noncomputable def hamiltonianEvolutionStepCost (t : ℝ) : ResourceCost :=
  ⟨0, 0, 0, 0, 0, ENNReal.ofReal |t|, 0⟩

/-- Accumulate gate profiles and, for each Hamiltonian evolution, an oracle-step charge together
with its absolute evolution time. -/
noncomputable def hamiltonianProgramResourceCost {I : Type*}
    (κg : Matrix I I ℂ → StepProfile) : List (HamiltonianQueryStep I) → ResourceCost
  | [] => 0
  | .gate U :: P => ResourceCost.ofMacroStep (κg U) + hamiltonianProgramResourceCost κg P
  | .evolve t :: P => (ResourceCost.ofOracleStep + hamiltonianEvolutionStepCost t) +
      hamiltonianProgramResourceCost κg P

/-- The query component of the Hamiltonian program ledger equals its Hamiltonian query count. -/
@[simp] theorem hamiltonianProgramResourceCost_queries {I : Type*}
    (κg : Matrix I I ℂ → StepProfile) (P : List (HamiltonianQueryStep I)) :
    (hamiltonianProgramResourceCost κg P).queries = HamiltonianQueryCount P := by
  induction P with
  | nil => rfl
  | cons s P ih =>
    cases s with
    | gate U =>
      simp [hamiltonianProgramResourceCost, HamiltonianQueryCount, ih]
    | evolve t =>
      simp [hamiltonianProgramResourceCost, HamiltonianQueryCount,
        hamiltonianEvolutionStepCost, ih]

/-- If every gate profile has zero evolution charge, the Hamiltonian-time ledger equals the
nonnegative extended-real value of total absolute evolution time. -/
theorem hamiltonianProgramResourceCost_hamiltonianTime {I : Type*}
    (κg : Matrix I I ℂ → StepProfile) (P : List (HamiltonianQueryStep I))
    (hκ : ∀ U, (κg U).evolve = 0) :
    (hamiltonianProgramResourceCost κg P).hamiltonianTime
      = ENNReal.ofReal (HamiltonianEvolutionTime P) := by
  induction P with
  | nil => simp [hamiltonianProgramResourceCost, HamiltonianEvolutionTime, ENNReal.ofReal_zero]
  | cons s P ih =>
    cases s with
    | gate U =>
      simp only [hamiltonianProgramResourceCost, ResourceCost.add_hamiltonianTime,
        ResourceCost.ofMacroStep_hamiltonianTime, hκ U, _root_.zero_add]
      rw [show HamiltonianEvolutionTime (HamiltonianQueryStep.gate U :: P)
          = HamiltonianEvolutionTime P from rfl]
      exact ih
    | evolve t =>
      simp only [hamiltonianProgramResourceCost, ResourceCost.add_hamiltonianTime,
        ResourceCost.ofOracleStep_hamiltonianTime, hamiltonianEvolutionStepCost]
      rw [show HamiltonianEvolutionTime (HamiltonianQueryStep.evolve t :: P)
          = |t| + HamiltonianEvolutionTime P from rfl,
        ENNReal.ofReal_add (abs_nonneg t) (hamiltonianEvolutionTime_nonneg P), _root_.zero_add,
        ih]

/-- A ledger of fresh copies, swaps, discards, and bit queries. -/
structure FreshCopyLedger where

  copies : ℕ

  swaps : ℕ

  discards : ℕ

  bitQueries : ℕ

/-- Convert a four-tuple of copy, swap, discard, and bit-query counts into a fresh-copy ledger. -/
def FreshCopyLedger.ofProd (q : ℕ × ℕ × ℕ × ℕ) : FreshCopyLedger :=
  ⟨q.1, q.2.1, q.2.2.1, q.2.2.2⟩

/-- Package the copy-based phase-estimation resource tuple as a fresh-copy ledger. -/
def copyQPELedgerAdapter {I : Type*} (n : ℕ) (C : Circuit I) : FreshCopyLedger :=
  FreshCopyLedger.ofProd (copyQPEProgramResources n C)

/-- Package the local copy-based phase-estimation resource tuple as a fresh-copy ledger. -/
def localCopyQPELedgerAdapter {I : Type*} (n s : ℕ) (C : Circuit I) : FreshCopyLedger :=
  FreshCopyLedger.ofProd (localCopyQPEProgramResources n s C)

/-- Package the numeric copy resource tuple as a fresh-copy ledger. -/
def numericCopyLedgerAdapter {I : Type*} (n b : ℕ) (C : Circuit I) : FreshCopyLedger :=
  FreshCopyLedger.ofProd (numericCopyResources n b C)

/-- Package the two-species phase-estimation resource tuple as a fresh-copy ledger. -/
def twoSpeciesLedgerAdapter (M n : ℕ) : FreshCopyLedger :=
  FreshCopyLedger.ofProd (twoSpeciesQPEResources M n)

/-- Package the resource counts for a sequence of fresh-copy angles as a fresh-copy ledger. -/
noncomputable def freshCopyCompositionLedgerAdapter (D : ℕ) (angles : List ℝ) :
    FreshCopyLedger :=
  FreshCopyLedger.ofProd (freshCopyResourceCounts D angles)

/-- A circuit approximates `target` within `ε` on every normalized input, is unitary, and has
derived resource cost bounded componentwise by `B`. -/
noncomputable def ImplementsWithBudget {I : Type*} [Fintype I] [DecidableEq I]
    (κ : Matrix I I ℂ → StepProfile) (oracle : Matrix I I ℂ) (C : Circuit I)
    (target : QState I → QState I) (ε : ℝ) (B : ResourceCost) : Prop :=
  (∀ ψ, Normalized ψ → ‖Run oracle C ψ - target ψ‖ ≤ ε) ∧
    IsUnitaryCircuit C ∧ derive κ C ≤ B

/-- Every oracle-dependent program satisfying `P` uses at least `F` queries for every oracle. -/
def QueryLowerBound {I : Type*}
    (P : (Matrix I I ℂ → Circuit I) → Prop) (F : ℕ) : Prop :=
  ∀ prog, P prog → ∀ oracle, F ≤ QueryCount (prog oracle)

/-- There is a positive constant giving the eventual one-sided upper bound `f n ≤ c * g n`. -/
def IsResourceBigO (f g : ℕ → ℝ) : Prop :=
  ∃ c N, 0 < c ∧ ∀ n ≥ N, f n ≤ c * g n

/-- There is a positive constant giving the eventual one-sided lower bound `c * g n ≤ f n`. -/
def IsResourceBigOmega (f g : ℕ → ℝ) : Prop :=
  ∃ c N, 0 < c ∧ ∀ n ≥ N, c * g n ≤ f n

/-- Both the one-sided resource upper and lower asymptotic comparisons hold. -/
def IsResourceBigTheta (f g : ℕ → ℝ) : Prop :=
  IsResourceBigO f g ∧ IsResourceBigOmega f g

/-- Local operations comprising matrix application, allocation of a specified width, release,
reset, and discard. -/
inductive LocalOp (I : Type)
  | applyU : Matrix I I ℂ → LocalOp I
  | alloc : ℕ → LocalOp I
  | release : LocalOp I
  | reset : LocalOp I
  | discard : LocalOp I

/-- A finite sequence of local operations represented by an empty program or an operation
followed by a continuation. -/
inductive LocalProgram (I : Type)
  | nil : LocalProgram I
  | op : LocalOp I → LocalProgram I → LocalProgram I

/-- Return the width of an allocation operation, and zero for every other local operation. -/
def localOpSpace {I : Type} : LocalOp I → ℕ
  | .alloc w => w
  | _ => 0

/-- The stack of outstanding allocation widths together with the largest total allocation
recorded so far. -/
structure LocalAllocState where

  allocs : List ℕ

  peak : ℕ

/-- Update the allocation stack and peak for one operation, pushing allocations and popping on
release, reset, or discard. -/
def localOpStep {I : Type} : LocalOp I → LocalAllocState → LocalAllocState
  | .alloc w, st => ⟨w :: st.allocs, max st.peak (w + st.allocs.sum)⟩
  | .release, st => ⟨st.allocs.tail, st.peak⟩
  | .reset, st => ⟨st.allocs.tail, st.peak⟩
  | .discard, st => ⟨st.allocs.tail, st.peak⟩
  | .applyU _, st => st

/-- Execute a local program's allocation-state updates from a supplied initial state. -/
def localProgramState {I : Type} : LocalProgram I → LocalAllocState → LocalAllocState
  | .nil, st => st
  | .op o rest, st => localProgramState rest (localOpStep o st)

/-- The peak allocation recorded when a local program starts with an empty stack and zero peak. -/
def localPeakSpace {I : Type} (p : LocalProgram I) : ℕ :=
  (localProgramState p ⟨[], 0⟩).peak

/-- A local program is balanced when execution from an empty allocation stack ends with an empty
stack. -/
def localProgramBalanced {I : Type} (p : LocalProgram I) : Prop :=
  (localProgramState p ⟨[], 0⟩).allocs = []

/-- Extract matrix-application gates from a local program in execution order. -/
def localProgramGates {I : Type} : LocalProgram I → List (Matrix I I ℂ)
  | .nil => []
  | .op (.applyU U) rest => U :: localProgramGates rest
  | .op _ rest => localProgramGates rest

/-- The product of a local program's matrix applications in execution order, ignoring
allocation-related operations. -/
noncomputable def localProgramMatrix {I : Type} [Fintype I] [DecidableEq I] :
    LocalProgram I → Matrix I I ℂ
  | .nil => 1
  | .op (.applyU U) rest => localProgramMatrix rest * U
  | .op _ rest => localProgramMatrix rest

/-- A local program is valid when every extracted matrix is unitary and its allocation stack is
balanced. -/
def LocalProgramValid {I : Type} [Fintype I] [DecidableEq I] (p : LocalProgram I) : Prop :=
  (∀ U ∈ localProgramGates p, U ∈ Matrix.unitaryGroup I ℂ) ∧ localProgramBalanced p

/-- The empty local program has zero peak space. -/
@[simp] theorem localPeakSpace_nil {I : Type} :
    localPeakSpace (LocalProgram.nil : LocalProgram I) = 0 :=
  rfl

end Qatlib.Concepts.QueryComplexity.DegreeMethod
