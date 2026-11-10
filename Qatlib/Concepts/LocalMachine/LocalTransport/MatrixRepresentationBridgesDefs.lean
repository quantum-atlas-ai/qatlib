/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SignalPrimitive.PhaseFrontend.ComputedPhaseQSVT
import Qatlib.Concepts.QsvtLinearSolve.RangeDataFit.ComputedRangeConsumers
import Qatlib.Concepts.QsvtCore.LinearSystems.FiniteInversePhaseProgram
import Qatlib.Concepts.LocalMachine.LocalTransport.LeastSquaresOutputSpec
import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownFrameLocalSynthesis
import Qatlib.Concepts.MatrixAccess.FrameFilterUse
import Qatlib.Concepts.LocalMachine.LocalTransport.ControlledQueryCircuit
import Qatlib.Concepts.LocalMachine.LocalTransport.NumericalDyadicPhase
import Qatlib.Concepts.SpectralSketch.NearIsometry
import Qatlib.Concepts.BlockEncoding.EncodingCore.SparseOverlapEncoding
import Qatlib.Concepts.BlockEncoding.EncodingCore.SparseOverlapEncodingConsumers
import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.OrderedSpectralPerturbation
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord

set_option autoImplicit false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Concepts.MonteCarloMean.PayoffRotation

open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.QsvtLinearSolve.RangeDataFit
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.QsvtCore.LinearSystems
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

namespace Qatlib.Concepts.LocalMachine.LocalTransport

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open scoped Classical BigOperators Matrix.Norms.L2Operator

structure BackendLedger where

  forwardCalls : ℕ

  backwardCalls : ℕ

  controlledCalls : ℕ

  positionCalls : ℕ

  valueCalls : ℕ

  elementaryGates : ℕ

  ancillaQubits : ℕ

  classicalBitOps : ℕ

  readoutBitOps : ℕ

  peakLiveQubits : ℕ

structure EffectivePhaseInput where

  coeffs : List ℚ

  deg : ℕ

  tol : ℚ

def EffectivePhaseInput.Admissible (e : EffectivePhaseInput) : Prop :=
  (realTarget e.coeffs).degree ≤ (e.deg : WithBot ℕ) ∧
    Qatlib.Concepts.QspSimulation.Achievability.HasRealParity e.deg (realTarget e.coeffs) ∧
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, |(realTarget e.coeffs).eval x| ≤ 1) ∧ 0 < e.tol

def rangePhaseInput (κ k : ℕ) : EffectivePhaseInput where
  coeffs := nativeRangeCoefficients (explicitInverseCutoff κ (k + 2))
  deg := 2 * explicitInverseCutoff κ (k + 2)
  tol := (1 / 2 : ℚ)^(k + 2)

def inversePhaseInput (n k : ℕ) : EffectivePhaseInput where
  coeffs := nativeInverseCoefficients n
  deg := 2 * n - 1
  tol := nativeInverseTolerance n k

def signPhaseInput (k : ℕ) (eps : ℚ) : EffectivePhaseInput where
  coeffs := rationalSignCoefficients k
  deg := 3^k
  tol := eps

structure PhaseRecoveryProgram where

  recover : EffectivePhaseInput → PhaseData

  bitCost : EffectivePhaseInput → ℕ

  responseRounds : EffectivePhaseInput → ℕ

  coefficientVisits : EffectivePhaseInput → ℕ

  costConst : ℕ
  degExp : ℕ
  tolExp : ℕ

def PhaseRecoveryProgram.PolyBounded (P : PhaseRecoveryProgram) : Prop :=
  0 < P.costConst ∧ ∀ e : EffectivePhaseInput,
    P.bitCost e ≤ P.costConst * (e.deg + 1)^P.degExp * (phaseToleranceBits e.tol + 1)^P.tolExp

def PhaseRecoveryProgram.CertifiedAt (P : PhaseRecoveryProgram)
    (e : EffectivePhaseInput) : Prop :=
  (P.recover e).phases.length = e.deg ∧
    ‖gaussianRatComplex (P.recover e).base‖ = 1 ∧
    (∀ z ∈ (P.recover e).phases, ‖gaussianRatComplex z‖ = 1) ∧
    (scoreData e.coeffs e.deg (P.recover e)).1.1 ≤ (1 / 2 : ℚ)^phaseToleranceBits e.tol ∧
    (∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |((responseP (gaussianRatComplex (P.recover e).base)
        ((P.recover e).phases.map gaussianRatComplex)).eval (x : ℂ)).re
        - (realTarget e.coeffs).eval x| ≤ (e.tol : ℝ)) ∧
    P.responseRounds e = e.deg ∧ P.coefficientVisits e = e.deg + 1

def PhaseRecoveryProgram.WordConnectedAt (P : PhaseRecoveryProgram)
    (e : EffectivePhaseInput) : Prop :=
  ∀ (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (U : Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ),
    ProjectedUnitaryEncoding A U L R →
    WellFormedAdjointCircuit (computedPhaseWord (rangeProjector R) (rangeProjector L)
        (P.recover e)) ∧
    adjointQueryCount (computedPhaseWord (rangeProjector R) (rangeProjector L)
        (P.recover e)) = e.deg ∧
    adjointGateCount (computedPhaseWord (rangeProjector R) (rangeProjector L)
        (P.recover e)) = e.deg + 1 ∧
    (e.deg % 2 = 1 →
      BlockEncoding (oddSingularTransform A
          (fun x => (((realTarget e.coeffs).eval x : ℝ) : ℂ)))
        (evaluate (parallelOracle U) (computedPhaseWord (rangeProjector R)
            (rangeProjector L) (P.recover e)))
        (averageFrame L) (averageFrame R) 1 (e.tol : ℝ)) ∧
    (e.deg % 2 = 0 →
      BlockEncoding (rightSingularTransform A
          (fun x => (((realTarget e.coeffs).eval x : ℝ) : ℂ)))
        (evaluate (parallelOracle Uᴴ) (computedPhaseWord (rangeProjector L)
            (rangeProjector R) (P.recover e)))
        (averageFrame R) (averageFrame R) 1 (e.tol : ℝ))

structure QuantizedMatrixInput (O I : Type) where

  num : O → I → ℤ × ℤ

  bits : ℕ

noncomputable def dyadicValue (p : ℤ × ℤ) (bits : ℕ) : ℂ :=
  (p.1 : ℂ) / (2 : ℂ)^bits + Complex.I * (p.2 : ℂ) / (2 : ℂ)^bits

noncomputable def QuantizedMatrixInput.matrix {O I : Type} (q : QuantizedMatrixInput O I) :
    Matrix O I ℂ := fun o i => dyadicValue (q.num o i) q.bits

def QuantizedMatrixInput.readBitCost {O I : Type} [Fintype O] [Fintype I]
    (q : QuantizedMatrixInput O I) : ℕ :=
  Fintype.card O * Fintype.card I * (2 * (q.bits + 1))

def derivedQuantityBitCost (entries bits : ℕ) : ℕ := (entries + 1) * 4 * (bits + 1)^3

structure FiniteFrameData where

  inputIndex : ℕ

  workspaceWires : ℕ

  num : Reg workspaceWires → Fin inputIndex → ℤ × ℤ

  bits : ℕ

  inputFrame : Matrix (Reg workspaceWires) (Fin inputIndex) ℂ

  gramErr : ℝ

noncomputable def FiniteFrameData.frame (d : FiniteFrameData) :
    Matrix (Reg d.workspaceWires) (Fin d.inputIndex) ℂ :=
  fun h i => dyadicValue (d.num h i) d.bits

def FiniteFrameData.IsCertified (d : FiniteFrameData) : Prop :=
  IsIsometry d.inputFrame ∧ ‖d.frameᴴ * d.frame - 1‖ ≤ d.gramErr ∧ d.gramErr < 1

noncomputable def polarCorrectionBitCost (α : ℝ) (bits : ℕ) : ℕ :=
  (Nat.ceil (1 / (1 - α)) + 1) * (12 * (bits + 2) + 40)

noncomputable def frameDataBitCost (d : FiniteFrameData) : ℕ :=
  (2^d.workspaceWires * 2^d.inputIndex) * 8 * (d.bits + 1)^3 +
    polarCorrectionBitCost d.gramErr d.bits

def continuousSynthesisGateBound (N : ℕ) : ℕ := 128 * (N + 1)^2 * 4^N

def IsWireLift {N : ℕ} (w : Finset (Fin N)) (M : Matrix (Reg N) (Reg N) ℂ) : Prop :=
  (∀ x y x' y' : Reg N, (∀ i ∈ w, x i = x' i ∧ y i = y' i) → M x y = M x' y') ∧
    (∀ x y : Reg N, (∃ i ∈ w, x i ≠ y i) → M x y = 0)

structure DynStep (N : ℕ) where

  wires : Finset (Fin N)

  op : Matrix (Reg N) (Reg N) ℂ

structure DynSchedule (N : ℕ) where

  initial : Finset (Fin N)

  steps : List (DynStep N)

def DynSchedule.liveCounts {N : ℕ} (s : DynSchedule N) : List ℕ :=
  (s.initial :: s.steps.map fun st => st.wires).map (·.card)

def DynSchedule.peak {N : ℕ} (s : DynSchedule N) : ℕ := s.liveCounts.foldl max 0

def DynSchedule.WellFormed {N : ℕ} (s : DynSchedule N) : Prop :=
  ∀ st ∈ s.steps, IsWireLift st.wires st.op

def DynSchedule.Realizes {N : ℕ} (s : DynSchedule N) (O : Matrix (Reg N) (Reg N) ℂ)
    (cs : List (AdjointStep (Reg N))) : Prop :=
  ∃ (core : List (DynStep N)) (release : DynStep N),
    s.steps = core ++ [release] ∧ core.length = cs.length ∧
      (∀ p ∈ core.zip cs, p.1.op = instructionMatrix O p.2) ∧
      release.op = 1 ∧ release.wires = s.initial ∧
      (s.steps.map (·.op)).foldl (fun acc M => M * acc) 1 = evaluate O cs

def flagRegEquiv (n : ℕ) : Reg (n + 1) ≃ Bool × Reg n :=
  (knownDataEquiv n).symm.trans (Equiv.prodComm (Reg n) Bool)

def flagRegisterMatrix {n : ℕ} (M : Matrix (Bool × Reg n) (Bool × Reg n) ℂ) :
    Matrix (Reg (n + 1)) (Reg (n + 1)) ℂ :=
  fun x y => M (flagRegEquiv n x) (flagRegEquiv n y)

noncomputable def flagRegStep {n : ℕ} :
    AdjointStep (Bool × Reg n) → AdjointStep (Reg (n + 1))
  | .gate G => .gate (flagRegisterMatrix G)
  | .forward => .forward
  | .backward => .backward

noncomputable def flagRegWord {n : ℕ} (cs : List (AdjointStep (Bool × Reg n))) :
    List (AdjointStep (Reg (n + 1))) := cs.map flagRegStep

inductive AccessDemand where

  | forward

  | backward

  | controlled
  deriving DecidableEq

structure UnknownAccess (H : Type) where

  unitary : Matrix H H ℂ

  suppliesControlled : Bool

inductive CompiledAccess (H : Type) where

  | forwardC (U : Matrix H H ℂ) : CompiledAccess H

  | backwardC (U : Matrix H H ℂ) : CompiledAccess H

  | controlledC (U : Matrix H H ℂ) : CompiledAccess H

  | unavailable : CompiledAccess H

def compileAccess {H : Type} (a : UnknownAccess H) : AccessDemand → CompiledAccess H
  | .forward => .forwardC a.unitary
  | .backward => .backwardC a.unitary
  | .controlled => if a.suppliesControlled then .controlledC a.unitary else .unavailable

def CompiledAccess.callCounts {H : Type} : CompiledAccess H → ℕ × ℕ × ℕ
  | .forwardC _ => (1, 0, 0)
  | .backwardC _ => (0, 1, 0)
  | .controlledC _ => (0, 0, 1)
  | .unavailable => (0, 0, 0)

noncomputable def CompiledAccess.realized {H : Type} [Fintype H] [DecidableEq H] :
    CompiledAccess H → Matrix (Bool × H) (Bool × H) ℂ
  | .forwardC U => parallelOracle U
  | .backwardC U => (parallelOracle U)ᴴ
  | .controlledC U => controlOracle U
  | .unavailable => 1

def compileAccessWord {H : Type} (a : UnknownAccess H) (ds : List AccessDemand) :
    List (CompiledAccess H) := ds.map (compileAccess a)

def compiledCallTotals {H : Type} : List (CompiledAccess H) → ℕ × ℕ × ℕ
  | [] => (0, 0, 0)
  | c :: cs =>
    let r := compiledCallTotals cs
    (r.1 + c.callCounts.1, r.2.1 + c.callCounts.2.1, r.2.2 + c.callCounts.2.2)

inductive SparsePipelineStep (n : ℕ) where

  | rowCall

  | colCall

  | valueCall

  | local (gs : List (ReflectionGate n))

noncomputable def sparseStepMatrix {n : ℕ} (rowO colO valO : Matrix (Reg n) (Reg n) ℂ) :
    SparsePipelineStep n → Matrix (Reg n) (Reg n) ℂ
  | .rowCall => rowO
  | .colCall => colO
  | .valueCall => valO
  | .local gs => reflectionProgramMatrix gs

noncomputable def sparsePipelineMatrix {n : ℕ} (rowO colO valO : Matrix (Reg n) (Reg n) ℂ)
    (ps : List (SparsePipelineStep n)) : Matrix (Reg n) (Reg n) ℂ :=
  ps.foldl (fun acc s => sparseStepMatrix rowO colO valO s * acc) 1

structure SparseOracleData (O I : Type) where

  rowPos : O → List I

  colPos : I → List O

  value : O → I → GaussianRat

  rowCallGates : ℕ

  colCallGates : ℕ

  valueCallGates : ℕ

  arithBits : ℕ

def SparseOracleData.matrix {O I : Type} (d : SparseOracleData O I) : Matrix O I ℂ :=
  fun o i => gaussianRatComplex (d.value o i)

def SparseOracleData.IsSparseBounded {O I : Type} (d : SparseOracleData O I)
    (k : ℕ) (b : ℝ) : Prop :=
  0 < k ∧ 0 < b ∧
    (∀ o, (d.rowPos o).length ≤ k ∧ (d.rowPos o).Nodup) ∧
    (∀ i, (d.colPos i).length ≤ k ∧ (d.colPos i).Nodup) ∧
    (∀ o i, i ∉ d.rowPos o → d.value o i = gzero) ∧
    (∀ o i, o ∉ d.colPos i → d.value o i = gzero) ∧
    (∀ o i, ‖gaussianRatComplex (d.value o i)‖ ≤ b)

def sparsePipelineLedger {O I : Type} (costs : SparseOracleData O I) {n : ℕ} :
    List (SparsePipelineStep n) → BackendLedger
  | [] => ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | .rowCall :: ps =>
    let r := sparsePipelineLedger costs ps
    ⟨r.forwardCalls, r.backwardCalls, r.controlledCalls, r.positionCalls + 1,
      r.valueCalls, r.elementaryGates + costs.rowCallGates, r.ancillaQubits,
      r.classicalBitOps, r.readoutBitOps, r.peakLiveQubits⟩
  | .colCall :: ps =>
    let r := sparsePipelineLedger costs ps
    ⟨r.forwardCalls, r.backwardCalls, r.controlledCalls, r.positionCalls + 1,
      r.valueCalls, r.elementaryGates + costs.colCallGates, r.ancillaQubits,
      r.classicalBitOps, r.readoutBitOps, r.peakLiveQubits⟩
  | .valueCall :: ps =>
    let r := sparsePipelineLedger costs ps
    ⟨r.forwardCalls, r.backwardCalls, r.controlledCalls, r.positionCalls,
      r.valueCalls + 1, r.elementaryGates + costs.valueCallGates, r.ancillaQubits,
      r.classicalBitOps + costs.arithBits, r.readoutBitOps, r.peakLiveQubits⟩
  | .local gs :: ps =>
    let r := sparsePipelineLedger costs ps
    ⟨r.forwardCalls, r.backwardCalls, r.controlledCalls, r.positionCalls,
      r.valueCalls, r.elementaryGates + gs.length, r.ancillaQubits,
      r.classicalBitOps, r.readoutBitOps, r.peakLiveQubits⟩

inductive MatrixInputModel where

  | explicit (rows cols : ℕ) (num : Fin rows → Fin cols → ℤ × ℤ) (bits : ℕ)

  | sparse (rows cols : ℕ) (items : List (ℕ × ℕ × ℤ × ℤ)) (bits : ℕ)

  | qram (rows cols : ℕ) (read : ℕ → ℕ → ℤ × ℤ) (bits : ℕ) (readCost : ℕ)

def MatrixInputModel.rows : MatrixInputModel → ℕ
  | .explicit r _ _ _ => r
  | .sparse r _ _ _ => r
  | .qram r _ _ _ _ => r

def MatrixInputModel.cols : MatrixInputModel → ℕ
  | .explicit _ c _ _ => c
  | .sparse _ c _ _ => c
  | .qram _ c _ _ _ => c

noncomputable def MatrixInputModel.describedMatrix (m : MatrixInputModel) :
    Matrix (Fin m.rows) (Fin m.cols) ℂ :=
  match m with
  | .explicit _ _ num bits => fun i j => dyadicValue (num i j) bits
  | .sparse _ _ items bits =>
    fun i j =>
      dyadicValue (match items.find? (fun t => t.1 = i.val ∧ t.2.1 = j.val) with
        | some t => t.2.2
        | none => (0, 0)) bits
  | .qram _ _ read bits _ => fun i j => dyadicValue (read i.val j.val) bits

def MatrixInputModel.readBitCost (m : MatrixInputModel) : ℕ :=
  match m with
  | .explicit rows cols _ bits => rows * cols * (2 * (bits + 1))
  | .sparse _ _ items bits => items.length * (2 * (bits + 1) + 4)
  | .qram rows cols _ bits readCost => readCost * rows * cols + rows * cols * (2 * (bits + 1))

def OnFiniteBackend {N : ℕ} (k : ℕ) (C : Circuit (Reg N)) : Prop :=
  ∀ U : Matrix (Reg N) (Reg N) ℂ, Step.gate U ∈ C →
    ∃ gs : List (LocalQFTGate N), U = numericalProgramMatrix k gs

noncomputable def finiteBackendErrorBound (k totalLocalGates : ℕ) : ℝ :=
  (totalLocalGates : ℝ) * ((2 : ℝ)⁻¹)^k

def numericalPhaseArithBits (k : ℕ) : ℕ := 2 * numericalPhaseSquarings k

end Qatlib.Concepts.LocalMachine.LocalTransport
