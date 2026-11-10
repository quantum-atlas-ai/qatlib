/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.List.GetD
import Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel
import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.ResourceDerivation
import Qatlib.Concepts.LocalMachine.LocalTransport.ControlledQueryCircuit
import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.LocalDyadicGate
import Qatlib.Concepts.NativeNumerics.PhaseSynthesis.FinitePhaseSynthesis
import Qatlib.Concepts.QsvtCore.QsVtMain.ConventionBridge
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
open Qatlib.Concepts.QsvtCore.QsVtMain
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

namespace Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum

open Matrix Polynomial
open scoped BigOperators Matrix.Norms.L2Operator

set_option autoImplicit false
set_option linter.unusedSectionVars false

section G8

variable {H : Type} [Fintype H] [DecidableEq H]

def ComplexConstantWordClassification (U P Q : Matrix H H ℂ) (c : ℂ) : Prop :=
  ∃ Φ : List ℝ, sourceDefWord U P Q Φ = c • 1 ∧
    (∀ Ψ : List ℝ, sourceDefWord U P Q Ψ = c • 1 → Φ.length ≤ Ψ.length) ∧
    Φ.length = if c = 1 then 0 else 1

def ComplexConstantReflectionCorrect (U P Q : Matrix H H ℂ) : Prop :=
  ComplexConstantWordClassification U P Q 1 ∧
    (∀ c : ℂ, Qatlib.Concepts.PhaseGeometry.Phase.IsPhase c →
      c = 1 ∨ ComplexConstantWordClassification U P Q c) ∧
    (∀ c : ℂ, c ≠ 1 → ¬ (∃ Φ : List ℝ, Φ = [] ∧ sourceDefWord U P Q Φ = c • 1))

end G8

noncomputable def evenPolyPart (p : Polynomial ℝ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (p.natDegree / 2 + 1), C (p.coeff (2 * k)) * X ^ k

noncomputable def oddPolyPart (p : Polynomial ℝ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range ((p.natDegree + 1) / 2), C (p.coeff (2 * k + 1)) * X ^ k

noncomputable def polyRealPart (P : Polynomial ℂ) : Polynomial ℝ :=
  ∑ n ∈ Finset.range (P.natDegree + 1), C (P.coeff n).re * X ^ n

noncomputable def polyImagPart (P : Polynomial ℂ) : Polynomial ℝ :=
  ∑ n ∈ Finset.range (P.natDegree + 1), C (P.coeff n).im * X ^ n

noncomputable def mixedParitySplit (P : Polynomial ℂ) :
    Polynomial ℝ × Polynomial ℝ × Polynomial ℝ × Polynomial ℝ :=
  (evenPolyPart (polyRealPart P), oddPolyPart (polyRealPart P),
    evenPolyPart (polyImagPart P), oddPolyPart (polyImagPart P))

structure MixedParityImplementation {H : Type} [Fintype H] [DecidableEq H]
    (U P Q : Matrix H H ℂ) (Pr : Polynomial ℂ) where

  phasesEven : List ℝ

  phasesOdd : List ℝ

  normalization : ℝ

  ancilla : ℕ

  error : ℝ

  queryEven : ℕ

  queryOdd : ℕ

structure PhaseInversionResult where

  phases : List GaussianRat

  residual : ℝ

  runtimeBits : ℕ

noncomputable def phaseInversionIdealPoly (coeffs : List ℂ) : Polynomial ℂ :=
  ∑ i ∈ Finset.range coeffs.length, C (coeffs.getD i 0) * X ^ i

noncomputable def PhaseInversionSuccess (d : ℕ) (coeffs : List ℂ) (ε : ℝ)
    (res : PhaseInversionResult) : Prop :=
  0 < ε ∧ ε ≤ 1 / 2 ∧ 0 ≤ res.residual ∧ res.residual ≤ ε ∧
    res.runtimeBits ≤ (d + Nat.ceil (Real.logb 2 (1 / ε)) + 8) ^ 5 ∧
    ∀ x : ℝ, |x| ≤ 1 →
      ‖(phaseInversionIdealPoly coeffs).eval (x : ℂ)
          - (Qatlib.Concepts.NativeNumerics.PhaseSynthesis.dataPolynomial res.phases).eval (x : ℂ)‖ ≤ ε

section Clause11

variable {H I : Type} [Fintype H] [Fintype I] [DecidableEq H] [DecidableEq I]

def controlledSector (b : Bool) (ψ : QState H) : QState (Bool × H) :=
  fun p => if p.1 = b then ψ p.2 else 0

structure FrameImplementation (F : Matrix H I ℂ) where

  seed : I → H

  prepareWord : Circuit H

  inverseWord : Circuit H

  controlledWord : Circuit (Bool × H)

  error : ℝ

  prepareQuery : ℕ

  prepareGate : ℕ

  inverseQuery : ℕ

  inverseGate : ℕ

  controlledQuery : ℕ

  controlledGate : ℕ

noncomputable def FrameTransportSuccess (F : Matrix H I ℂ)
    (impl : FrameImplementation F) (ε : ℝ) : Prop :=
  Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry F → 0 < ε →
    0 ≤ impl.error ∧ impl.error ≤ ε ∧ Function.Injective impl.seed ∧
    (∀ i : I, ‖Run (1 : Matrix H H ℂ) impl.prepareWord (Qatlib.Foundations.PureStateMath.Ket (impl.seed i))
        - (fun j => F j i)‖ ≤ impl.error) ∧
    (∀ ψ : QState H,
      ‖Run (1 : Matrix H H ℂ) impl.inverseWord
          (Run (1 : Matrix H H ℂ) impl.prepareWord ψ) - ψ‖ ≤ impl.error) ∧
    (∀ (b : Bool) (ψ : QState H),
      ‖Run (1 : Matrix (Bool × H) (Bool × H) ℂ) impl.controlledWord
          (controlledSector b ψ)
          - controlledSector b (if b then
              Run (1 : Matrix H H ℂ) impl.prepareWord ψ else ψ)‖ ≤ impl.error) ∧
    QueryCount impl.prepareWord = impl.prepareQuery ∧
    GateCount impl.prepareWord = impl.prepareGate ∧
    QueryCount impl.inverseWord = impl.inverseQuery ∧
    GateCount impl.inverseWord = impl.inverseGate ∧
    QueryCount impl.controlledWord = impl.controlledQuery ∧
    GateCount impl.controlledWord = impl.controlledGate

end Clause11

structure FiniteBackendCompilation (w : ℕ) where

  gates : List (LocalQFTGate w)

  totalError : ℝ

  gateCount : ℕ

  bitTime : ℕ

  peakSpace : ℕ

noncomputable def finiteBackendRealizes {w : ℕ} (target : Matrix (Reg w) (Reg w) ℂ)
    (comp : FiniteBackendCompilation w) : Prop :=
  0 ≤ comp.totalError ∧ target ∈ Matrix.unitaryGroup (Reg w) ℂ ∧
    ‖localProgramMatrix comp.gates - target‖ ≤ comp.totalError ∧
    comp.gateCount = comp.gates.length ∧
    comp.bitTime ≤ (w + comp.gates.length + 1) ^ 3 ∧
    comp.peakSpace ≤ w + 1

section Clause14

variable {I : Type} [Fintype I] [DecidableEq I]

noncomputable def SparseAccessImplementationSpec
    (valueOracle : Matrix I I ℂ)
    (controlledOracle : Matrix (Bool × I) (Bool × I) ℂ)
    (adjointOracle : Matrix I I ℂ)
    (budget : ResourceCost) : Prop :=
  controlledOracle = Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle valueOracle ∧
    adjointOracle = valueOracleᴴ ∧
    (∃ Cv : Circuit I, IsUnitaryCircuit Cv ∧ QueryCount Cv ≤ budget.queries ∧
      GateCount Cv ≤ budget.macroGates ∧ Size Cv ≤ budget.depth ∧
      ∀ ψ : QState I, Run valueOracle Cv ψ = ApplyGate valueOracle ψ) ∧
    (∃ Cc : Circuit (Bool × I), IsUnitaryCircuit Cc ∧ QueryCount Cc ≤ budget.queries ∧
      GateCount Cc ≤ budget.macroGates ∧ Size Cc ≤ budget.depth ∧
      ∀ φ : QState (Bool × I),
        Run controlledOracle Cc φ = ApplyGate controlledOracle φ) ∧
    (∃ Ca : Circuit I, IsUnitaryCircuit Ca ∧ QueryCount Ca ≤ budget.queries ∧
      GateCount Ca ≤ budget.macroGates ∧ Size Ca ≤ budget.depth ∧
      ∀ ψ : QState I, Run adjointOracle Ca ψ = ApplyGate adjointOracle ψ)

end Clause14

section PaidWalk

variable {D : ℕ}

noncomputable def PhysicalWorkspaceSpec (ε : ℝ) (ideal : Operator D)
    (channel : QuantumChannel D D) (peakSpace ancilla retryBudget : ℕ) : Prop :=
  0 < ε ∧ ideal ∈ Matrix.unitaryGroup (Fin D) ℂ ∧
    (∀ ρ : Operator D, IsDensityOperator ρ →
      SchattenOne (channel.map ρ - ideal * ρ * idealᴴ) ≤ ε) ∧
    ancilla ≤ peakSpace ∧ peakSpace ≤ D + ancilla ∧ retryBudget ≤ peakSpace

end PaidWalk

end Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
