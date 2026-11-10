/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding
import Qatlib.Concepts.QspSimulation.Achievability.CircuitWellFormed
import Qatlib.Concepts.QsvtCore.QueryLowerBound.SubroutineExpansion
import Qatlib.Concepts.LocalMachine.LocalTransport.ControlledQueryCircuit
import Qatlib.Concepts.QspSimulation.JacobiAnger.ComputedSignalSimulation
import Mathlib.Data.Fintype.Pi
import Qatlib.Concepts.SignalPrimitive.GridGradient.Basic
import Qatlib.Concepts.GradientOracle.ReadoutWindow.ValueOracleGradientPrecision
import Qatlib.Concepts.GradientOracle.FullRange.FullRangeGradientLaws
import Qatlib.Concepts.GradientOracle.ReadoutTools.AlmostAffineGradient
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.LocalQFTReadout

open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SignalPrimitive.GridGradient
open Qatlib.Concepts.GradientOracle.FullRange
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.JacobiAnger
open Qatlib.Concepts.GradientOracle.ReadoutTools
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.HspRecovery.ReductionCore

open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped BigOperators

def cleanFrame {X A : Type*} [DecidableEq X] [DecidableEq A] (a₀ : A) :
    Matrix (X × A) X ℂ := fun xa x => if xa = (x,a₀) then 1 else 0

def goodReflection {X A : Type*} [DecidableEq X] [DecidableEq A] (good : Finset A) :
    Matrix (X × A) (X × A) ℂ := Matrix.diagonal (fun xa => if xa.2 ∈ good then -1 else 1)

def probabilityMass {X A : Type*} (U : Matrix (X × A) (X × A) ℂ)
    (a₀ : A) (good : Finset A) (x : X) : ℝ :=
  ∑ a ∈ good, Complex.normSq (U (x,a) (x,a₀))

def reflectionWord {X A : Type*} [DecidableEq X] [DecidableEq A] (good : Finset A) :
    List (AdjointStep (X × A)) := [.backward, .gate (goodReflection good), .forward]

def controlledReflectionWord {X A : Type*} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (good : Finset A) :
    List (AdjointStep (Bool × (X × A))) :=
  [.backward, .gate (controlOracle (goodReflection good)), .forward]

def expandReflection {X A : Type} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (good : Finset A)
    (word : List (AdjointStep (X × A))) : List (AdjointStep (X × A)) :=
  substituteAdjointCircuit (reflectionWord good) word

def probabilityPrimitiveOracle {X A : Type} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (U : Matrix (X × A) (X × A) ℂ) :
    Matrix (Bool × (Bool × (Bool × (X × A)))) (Bool × (Bool × (Bool × (X × A)))) ℂ :=
  TensorGate 1 (parallelOracle (J := Bool) (parallelOracle (J := Bool) U))

def probabilitySimulationBody {X A : Type} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (good : Finset A) :
    List (AdjointStep (Bool × (Bool × (Bool × (X × A))))) :=
  [.backward, .gate (TensorGate 1
    (controlOracle (parallelOracle (J := Bool) (goodReflection (X := X) good)))), .forward]

def probabilitySimulationWord {X A : Type} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (a₀ : A) (good : Finset A) (t : ℚ) (k : ℕ) :
    List (AdjointStep (Bool × (Bool × (Bool × (X × A))))) :=
  substituteAdjointCircuit (probabilitySimulationBody good)
    (computedSignalWord (cleanFrame (X := X) a₀) t k)

def probabilityPhaseWord {X A : Type} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (a₀ : A) (good : Finset A) (k : ℕ) :
    List (AdjointStep (Bool × (Bool × (Bool × (X × A))))) :=
  .gate (Complex.exp (Complex.I/2) • 1) :: probabilitySimulationWord (X := X) a₀ good (1/2) k

def averagePreparation : Matrix Bool Bool ℂ := fun b c =>
  realPartAmplitude b * if b && c then -1 else 1

def signalPreparationWord (H : Type) [Fintype H] [DecidableEq H] :
    List (AdjointStep (Bool × (Bool × (Bool × H)))) :=
  [.gate (TensorGate 1 (TensorGate averagePreparation (1 : Matrix (Bool × H) (Bool × H) ℂ))),
   .gate (TensorGate 1 (TensorGate 1 (TensorGate averagePreparation (1 : Matrix H H ℂ))))]

def zeroSignalFrame {X A : Type} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (a₀ : A) :
    Matrix (Bool × (Bool × (Bool × (X × A)))) X ℂ :=
  scaleEightFrame (scaleEightFrame (scaleEightFrame (cleanFrame (X := X) a₀)))

def cleanProbabilityPhaseWord {X A : Type} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (a₀ : A) (good : Finset A) (k : ℕ) :
    List (AdjointStep (Bool × (Bool × (Bool × (X × A))))) :=
  adjointCircuit (signalPreparationWord (X × A)) ++
    probabilityPhaseWord (X := X) a₀ good k ++ signalPreparationWord (X × A)

def phasePrecision (ε : ℚ) : ℕ := Nat.clog 2 (max 1 ⌈ε⁻¹⌉₊)

end Qatlib.Concepts.HspRecovery.ReductionCore

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.HspRecovery.Reduction.GradientOracle

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

noncomputable def dyadicGridPhase (M : ℕ) (z : Fin M) : ℝ := (z.val : ℝ) / (M : ℝ)

def HasDyadicRecord (k : ℕ) (θ : ℝ) : Prop := ∃ n : ℤ, θ = n / (2 : ℝ) ^ k

noncomputable def dyadicDecode (lo s : ℝ) (K k : ℕ) (v : ZMod (2 ^ (K + k))) : ℝ :=
  lo + (v.val : ℝ) / (s * (2 : ℝ) ^ k)

noncomputable def readoutErrorBudget (d M : ℕ) (w δ : ℝ) : ℝ :=
  16 * (d : ℝ) / ((M : ℝ) * w) + 4 * Real.pi * δ

noncomputable def medianComparisonCount (d M : ℕ) (r : ℕ)
    (ω : Fin (2 * r + 1) → GradientGrid d M) : ℕ :=
  ∑ j : Fin d, (gradientMedianCounted r ω j).2

def readoutIntegerBits (K k : ℕ) : ℕ := K + k

def readoutSpaceBits (d M K k : ℕ) : ℕ :=
  d * Nat.clog 2 (max 2 M) + K + k

end Qatlib.Concepts.HspRecovery.Reduction.GradientOracle
