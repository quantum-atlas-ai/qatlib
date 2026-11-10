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
set_option warningAsError false
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

theorem le_refl (a : ResourceCost) : a ≤ a :=
  ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩

def adjointWordResourceCost {H : Type*} (κg : Matrix H H ℂ → StepProfile) :
    List (AdjointStep H) → ResourceCost
  | [] => 0
  | .gate V :: W => ResourceCost.ofMacroStep (κg V) + adjointWordResourceCost κg W
  | .forward :: W => ResourceCost.ofOracleStep + adjointWordResourceCost κg W
  | .backward :: W => ResourceCost.ofOracleStep + adjointWordResourceCost κg W

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

noncomputable def hamiltonianEvolutionStepCost (t : ℝ) : ResourceCost :=
  ⟨0, 0, 0, 0, 0, ENNReal.ofReal |t|, 0⟩

noncomputable def hamiltonianProgramResourceCost {I : Type*}
    (κg : Matrix I I ℂ → StepProfile) : List (HamiltonianQueryStep I) → ResourceCost
  | [] => 0
  | .gate U :: P => ResourceCost.ofMacroStep (κg U) + hamiltonianProgramResourceCost κg P
  | .evolve t :: P => (ResourceCost.ofOracleStep + hamiltonianEvolutionStepCost t) +
      hamiltonianProgramResourceCost κg P

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

structure FreshCopyLedger where

  copies : ℕ

  swaps : ℕ

  discards : ℕ

  bitQueries : ℕ

def FreshCopyLedger.ofProd (q : ℕ × ℕ × ℕ × ℕ) : FreshCopyLedger :=
  ⟨q.1, q.2.1, q.2.2.1, q.2.2.2⟩

def copyQPELedgerAdapter {I : Type*} (n : ℕ) (C : Circuit I) : FreshCopyLedger :=
  FreshCopyLedger.ofProd (copyQPEProgramResources n C)

def localCopyQPELedgerAdapter {I : Type*} (n s : ℕ) (C : Circuit I) : FreshCopyLedger :=
  FreshCopyLedger.ofProd (localCopyQPEProgramResources n s C)

def numericCopyLedgerAdapter {I : Type*} (n b : ℕ) (C : Circuit I) : FreshCopyLedger :=
  FreshCopyLedger.ofProd (numericCopyResources n b C)

def twoSpeciesLedgerAdapter (M n : ℕ) : FreshCopyLedger :=
  FreshCopyLedger.ofProd (twoSpeciesQPEResources M n)

noncomputable def freshCopyCompositionLedgerAdapter (D : ℕ) (angles : List ℝ) :
    FreshCopyLedger :=
  FreshCopyLedger.ofProd (freshCopyResourceCounts D angles)

noncomputable def ImplementsWithBudget {I : Type*} [Fintype I] [DecidableEq I]
    (κ : Matrix I I ℂ → StepProfile) (oracle : Matrix I I ℂ) (C : Circuit I)
    (target : QState I → QState I) (ε : ℝ) (B : ResourceCost) : Prop :=
  (∀ ψ, Normalized ψ → ‖Run oracle C ψ - target ψ‖ ≤ ε) ∧
    IsUnitaryCircuit C ∧ derive κ C ≤ B

def QueryLowerBound {I : Type*}
    (P : (Matrix I I ℂ → Circuit I) → Prop) (F : ℕ) : Prop :=
  ∀ prog, P prog → ∀ oracle, F ≤ QueryCount (prog oracle)

def IsResourceBigO (f g : ℕ → ℝ) : Prop :=
  ∃ c N, 0 < c ∧ ∀ n ≥ N, f n ≤ c * g n

def IsResourceBigOmega (f g : ℕ → ℝ) : Prop :=
  ∃ c N, 0 < c ∧ ∀ n ≥ N, c * g n ≤ f n

def IsResourceBigTheta (f g : ℕ → ℝ) : Prop :=
  IsResourceBigO f g ∧ IsResourceBigOmega f g

inductive LocalOp (I : Type)
  | applyU : Matrix I I ℂ → LocalOp I
  | alloc : ℕ → LocalOp I
  | release : LocalOp I
  | reset : LocalOp I
  | discard : LocalOp I

inductive LocalProgram (I : Type)
  | nil : LocalProgram I
  | op : LocalOp I → LocalProgram I → LocalProgram I

def localOpSpace {I : Type} : LocalOp I → ℕ
  | .alloc w => w
  | _ => 0

structure LocalAllocState where

  allocs : List ℕ

  peak : ℕ

def localOpStep {I : Type} : LocalOp I → LocalAllocState → LocalAllocState
  | .alloc w, st => ⟨w :: st.allocs, max st.peak (w + st.allocs.sum)⟩
  | .release, st => ⟨st.allocs.tail, st.peak⟩
  | .reset, st => ⟨st.allocs.tail, st.peak⟩
  | .discard, st => ⟨st.allocs.tail, st.peak⟩
  | .applyU _, st => st

def localProgramState {I : Type} : LocalProgram I → LocalAllocState → LocalAllocState
  | .nil, st => st
  | .op o rest, st => localProgramState rest (localOpStep o st)

def localPeakSpace {I : Type} (p : LocalProgram I) : ℕ :=
  (localProgramState p ⟨[], 0⟩).peak

def localProgramBalanced {I : Type} (p : LocalProgram I) : Prop :=
  (localProgramState p ⟨[], 0⟩).allocs = []

def localProgramGates {I : Type} : LocalProgram I → List (Matrix I I ℂ)
  | .nil => []
  | .op (.applyU U) rest => U :: localProgramGates rest
  | .op _ rest => localProgramGates rest

noncomputable def localProgramMatrix {I : Type} [Fintype I] [DecidableEq I] :
    LocalProgram I → Matrix I I ℂ
  | .nil => 1
  | .op (.applyU U) rest => localProgramMatrix rest * U
  | .op _ rest => localProgramMatrix rest

def LocalProgramValid {I : Type} [Fintype I] [DecidableEq I] (p : LocalProgram I) : Prop :=
  (∀ U ∈ localProgramGates p, U ∈ Matrix.unitaryGroup I ℂ) ∧ localProgramBalanced p

@[simp] theorem localPeakSpace_nil {I : Type} :
    localPeakSpace (LocalProgram.nil : LocalProgram I) = 0 :=
  rfl

end Qatlib.Concepts.QueryComplexity.DegreeMethod
