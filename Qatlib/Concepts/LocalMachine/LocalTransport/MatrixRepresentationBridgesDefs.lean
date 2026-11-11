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

/-!
# Data for matrix representation and resource bridges

This module defines the records and predicates used to connect finite matrix descriptions with
phase-response words, frame correction, sparse encodings, and numerical circuit backends.
`EffectivePhaseInput` and `PhaseRecoveryProgram` separate input conditions, recovered phase
certificates, circuit connections, and recorded costs for the singular value transformation
setting of [GilyenSuLowWiebe2019].

`FiniteFrameData`, `DynSchedule`, `UnknownAccess`, `SparseOracleData`, and `MatrixInputModel`
specify representation and bookkeeping interfaces. Their associated predicates state the
required mathematical conditions explicitly; the records alone do not impose those conditions.

## Main statements

* `PhaseRecoveryProgram.WordConnectedAt`: specify well-formed response words, exact counts, and
  parity-dependent encodings.
* `FiniteFrameData.IsCertified`: require an isometric input frame and a Gram error below one.
* `DynSchedule.Realizes`: relate schedule operators to an adjoint-query word.
* `OnFiniteBackend`: require each fixed gate to have a numerical local-gate representation.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

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

/-- Recorded counts for oracle calls, elementary gates, ancillas, classical and readout bit
operations, and peak live qubits. -/
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

/-- A rational polynomial coefficient list, degree parameter, and rational tolerance for phase
recovery. -/
structure EffectivePhaseInput where

  coeffs : List ℚ

  deg : ℕ

  tol : ℚ

/-- The target polynomial has degree at most `deg`, the prescribed parity, absolute value at
most one on `[-1, 1]`, and positive tolerance. -/
def EffectivePhaseInput.Admissible (e : EffectivePhaseInput) : Prop :=
  (realTarget e.coeffs).degree ≤ (e.deg : WithBot ℕ) ∧
    Qatlib.Concepts.QspSimulation.Achievability.HasRealParity e.deg (realTarget e.coeffs) ∧
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, |(realTarget e.coeffs).eval x| ≤ 1) ∧ 0 < e.tol

/-- The rational range-response input built from the explicit inverse cutoff, with even degree
and tolerance `2^(-(k + 2))`. -/
def rangePhaseInput (κ k : ℕ) : EffectivePhaseInput where
  coeffs := nativeRangeCoefficients (explicitInverseCutoff κ (k + 2))
  deg := 2 * explicitInverseCutoff κ (k + 2)
  tol := (1 / 2 : ℚ)^(k + 2)

/-- The rational inverse-response input with degree `2 * n - 1` and the native inverse
tolerance. -/
def inversePhaseInput (n k : ℕ) : EffectivePhaseInput where
  coeffs := nativeInverseCoefficients n
  deg := 2 * n - 1
  tol := nativeInverseTolerance n k

/-- The rational sign-response input with degree `3^k` and the supplied tolerance. -/
def signPhaseInput (k : ℕ) (eps : ℚ) : EffectivePhaseInput where
  coeffs := rationalSignCoefficients k
  deg := 3^k
  tol := eps

/-- A phase recovery function together with recorded bit cost, response and coefficient
counters, and polynomial-bound parameters. -/
structure PhaseRecoveryProgram where

  recover : EffectivePhaseInput → PhaseData

  bitCost : EffectivePhaseInput → ℕ

  responseRounds : EffectivePhaseInput → ℕ

  coefficientVisits : EffectivePhaseInput → ℕ

  costConst : ℕ
  degExp : ℕ
  tolExp : ℕ

/-- The recorded bit cost is bounded by a polynomial in the degree parameter and tolerance-bit
parameter, with positive cost coefficient. -/
def PhaseRecoveryProgram.PolyBounded (P : PhaseRecoveryProgram) : Prop :=
  0 < P.costConst ∧ ∀ e : EffectivePhaseInput,
    P.bitCost e ≤ P.costConst * (e.deg + 1)^P.degExp * (phaseToleranceBits e.tol + 1)^P.tolExp

/-- Recovered phases have the prescribed length and unit modulus, satisfy the score and uniform
real-response error bounds, and have the specified recorded counters. -/
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

/-- Recovered phase words are well formed with exact degree-based query and gate counts, and
give the prescribed odd or even singular-transform block encodings. -/
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

/-- Integer pairs for complex matrix entries together with a common dyadic denominator exponent. -/
structure QuantizedMatrixInput (O I : Type) where

  num : O → I → ℤ × ℤ

  bits : ℕ

/-- The complex number with real and imaginary integer numerators divided by `2^bits`. -/
noncomputable def dyadicValue (p : ℤ × ℤ) (bits : ℕ) : ℂ :=
  (p.1 : ℂ) / (2 : ℂ)^bits + Complex.I * (p.2 : ℂ) / (2 : ℂ)^bits

/-- Interpret the integer-pair matrix data using the common dyadic denominator. -/
noncomputable def QuantizedMatrixInput.matrix {O I : Type} (q : QuantizedMatrixInput O I) :
    Matrix O I ℂ := fun o i => dyadicValue (q.num o i) q.bits

/-- The recorded dense read cost, equal to the number of entries times `2 * (bits + 1)`. -/
def QuantizedMatrixInput.readBitCost {O I : Type} [Fintype O] [Fintype I]
    (q : QuantizedMatrixInput O I) : ℕ :=
  Fintype.card O * Fintype.card I * (2 * (q.bits + 1))

/-- The cost expression `(entries + 1) * 4 * (bits + 1)^3` for derived quantities. -/
def derivedQuantityBitCost (entries bits : ℕ) : ℕ := (entries + 1) * 4 * (bits + 1)^3

/-- A dyadic frame description with column count, workspace width, reference input frame, and
recorded Gram error. -/
structure FiniteFrameData where

  inputIndex : ℕ

  workspaceWires : ℕ

  num : Reg workspaceWires → Fin inputIndex → ℤ × ℤ

  bits : ℕ

  inputFrame : Matrix (Reg workspaceWires) (Fin inputIndex) ℂ

  gramErr : ℝ

/-- Decode the dyadic entries of the finite frame description into a complex matrix. -/
noncomputable def FiniteFrameData.frame (d : FiniteFrameData) :
    Matrix (Reg d.workspaceWires) (Fin d.inputIndex) ℂ :=
  fun h i => dyadicValue (d.num h i) d.bits

/-- The reference input frame is isometric and the decoded frame has Gram defect bounded by
`gramErr`, with `gramErr < 1`. -/
def FiniteFrameData.IsCertified (d : FiniteFrameData) : Prop :=
  IsIsometry d.inputFrame ∧ ‖d.frameᴴ * d.frame - 1‖ ≤ d.gramErr ∧ d.gramErr < 1

/-- The recorded polar-correction cost expression depending on the reciprocal Gram gap and entry
precision. -/
noncomputable def polarCorrectionBitCost (α : ℝ) (bits : ℕ) : ℕ :=
  (Nat.ceil (1 / (1 - α)) + 1) * (12 * (bits + 2) + 40)

/-- The combined frame-data processing and polar-correction cost expression. -/
noncomputable def frameDataBitCost (d : FiniteFrameData) : ℕ :=
  (2^d.workspaceWires * 2^d.inputIndex) * 8 * (d.bits + 1)^3 +
    polarCorrectionBitCost d.gramErr d.bits

/-- The continuous synthesis gate bound `128 * (N + 1)^2 * 4^N`. -/
def continuousSynthesisGateBound (N : ℕ) : ℕ := 128 * (N + 1)^2 * 4^N

/-- The property that entries depend only on the `w` coordinates of both indices and vanish
whenever those indices disagree on a coordinate in `w`. -/
def IsWireLift {N : ℕ} (w : Finset (Fin N)) (M : Matrix (Reg N) (Reg N) ℂ) : Prop :=
  (∀ x y x' y' : Reg N, (∀ i ∈ w, x i = x' i ∧ y i = y' i) → M x y = M x' y') ∧
    (∀ x y : Reg N, (∃ i ∈ w, x i ≠ y i) → M x y = 0)

/-- A dynamic schedule step consisting of a declared wire set and an operator matrix. -/
structure DynStep (N : ℕ) where

  wires : Finset (Fin N)

  op : Matrix (Reg N) (Reg N) ℂ

/-- A declared initial wire set together with a list of dynamic operator steps. -/
structure DynSchedule (N : ℕ) where

  initial : Finset (Fin N)

  steps : List (DynStep N)

/-- The cardinalities of the initial wire set and the wire sets of all schedule steps. -/
def DynSchedule.liveCounts {N : ℕ} (s : DynSchedule N) : List ℕ :=
  (s.initial :: s.steps.map fun st => st.wires).map (·.card)

/-- The maximum of the recorded live-wire counts, computed by a fold starting at zero. -/
def DynSchedule.peak {N : ℕ} (s : DynSchedule N) : ℕ := s.liveCounts.foldl max 0

/-- Every scheduled operator satisfies `IsWireLift` for its declared wire set. -/
def DynSchedule.WellFormed {N : ℕ} (s : DynSchedule N) : Prop :=
  ∀ st ∈ s.steps, IsWireLift st.wires st.op

/-- The schedule matches the instruction matrices of a circuit, ends with an identity release
step on the initial wires, and has total product equal to the circuit evaluation. -/
def DynSchedule.Realizes {N : ℕ} (s : DynSchedule N) (O : Matrix (Reg N) (Reg N) ℂ)
    (cs : List (AdjointStep (Reg N))) : Prop :=
  ∃ (core : List (DynStep N)) (release : DynStep N),
    s.steps = core ++ [release] ∧ core.length = cs.length ∧
      (∀ p ∈ core.zip cs, p.1.op = instructionMatrix O p.2) ∧
      release.op = 1 ∧ release.wires = s.initial ∧
      (s.steps.map (·.op)).foldl (fun acc M => M * acc) 1 = evaluate O cs

/-- Identify an `(n + 1)`-qubit register with a Boolean flag and an `n`-qubit register. -/
def flagRegEquiv (n : ℕ) : Reg (n + 1) ≃ Bool × Reg n :=
  (knownDataEquiv n).symm.trans (Equiv.prodComm (Reg n) Bool)

/-- Reindex a matrix on a flag-register pair as a matrix on a single larger register. -/
def flagRegisterMatrix {n : ℕ} (M : Matrix (Bool × Reg n) (Bool × Reg n) ℂ) :
    Matrix (Reg (n + 1)) (Reg (n + 1)) ℂ :=
  fun x y => M (flagRegEquiv n x) (flagRegEquiv n y)

/-- Reindex the fixed gate of a flagged adjoint-query instruction while retaining the direction
of oracle queries. -/
noncomputable def flagRegStep {n : ℕ} :
    AdjointStep (Bool × Reg n) → AdjointStep (Reg (n + 1))
  | .gate G => .gate (flagRegisterMatrix G)
  | .forward => .forward
  | .backward => .backward

/-- Reindex every instruction of a flagged adjoint-query word onto a single larger register. -/
noncomputable def flagRegWord {n : ℕ} (cs : List (AdjointStep (Bool × Reg n))) :
    List (AdjointStep (Reg (n + 1))) := cs.map flagRegStep

/-- A request for forward, backward, or controlled oracle access. -/
inductive AccessDemand where

  | forward

  | backward

  | controlled
  deriving DecidableEq

/-- A matrix supplied through an access interface and a Boolean indicating whether controlled
access is available. -/
structure UnknownAccess (H : Type) where

  unitary : Matrix H H ℂ

  suppliesControlled : Bool

/-- A compiled forward, backward, or controlled matrix call, or a marker for unavailable access. -/
inductive CompiledAccess (H : Type) where

  | forwardC (U : Matrix H H ℂ) : CompiledAccess H

  | backwardC (U : Matrix H H ℂ) : CompiledAccess H

  | controlledC (U : Matrix H H ℂ) : CompiledAccess H

  | unavailable : CompiledAccess H

/-- Translate an access demand to the supplied matrix call, marking a controlled demand
unavailable when controlled access is absent. -/
def compileAccess {H : Type} (a : UnknownAccess H) : AccessDemand → CompiledAccess H
  | .forward => .forwardC a.unitary
  | .backward => .backwardC a.unitary
  | .controlled => if a.suppliesControlled then .controlledC a.unitary else .unavailable

/-- The forward, backward, and controlled call-count triple of a compiled access instruction. -/
def CompiledAccess.callCounts {H : Type} : CompiledAccess H → ℕ × ℕ × ℕ
  | .forwardC _ => (1, 0, 0)
  | .backwardC _ => (0, 1, 0)
  | .controlledC _ => (0, 0, 1)
  | .unavailable => (0, 0, 0)

/-- Interpret compiled access on a Boolean-extended register, using the identity for unavailable
access. -/
noncomputable def CompiledAccess.realized {H : Type} [Fintype H] [DecidableEq H] :
    CompiledAccess H → Matrix (Bool × H) (Bool × H) ℂ
  | .forwardC U => parallelOracle U
  | .backwardC U => (parallelOracle U)ᴴ
  | .controlledC U => controlOracle U
  | .unavailable => 1

/-- Compile every access demand in a list using the given access interface. -/
def compileAccessWord {H : Type} (a : UnknownAccess H) (ds : List AccessDemand) :
    List (CompiledAccess H) := ds.map (compileAccess a)

/-- Sum the forward, backward, and controlled call counts over a compiled access word. -/
def compiledCallTotals {H : Type} : List (CompiledAccess H) → ℕ × ℕ × ℕ
  | [] => (0, 0, 0)
  | c :: cs =>
    let r := compiledCallTotals cs
    (r.1 + c.callCounts.1, r.2.1 + c.callCounts.2.1, r.2.2 + c.callCounts.2.2)

/-- A sparse-access pipeline step: row-position call, column-position call, value call, or local
reflection-gate program. -/
inductive SparsePipelineStep (n : ℕ) where

  | rowCall

  | colCall

  | valueCall

  | local (gs : List (ReflectionGate n))

/-- Interpret a sparse pipeline step using the supplied oracle matrices or its local
reflection-program matrix. -/
noncomputable def sparseStepMatrix {n : ℕ} (rowO colO valO : Matrix (Reg n) (Reg n) ℂ) :
    SparsePipelineStep n → Matrix (Reg n) (Reg n) ℂ
  | .rowCall => rowO
  | .colCall => colO
  | .valueCall => valO
  | .local gs => reflectionProgramMatrix gs

/-- Multiply sparse pipeline step matrices in execution order, with each new matrix acting on
the left. -/
noncomputable def sparsePipelineMatrix {n : ℕ} (rowO colO valO : Matrix (Reg n) (Reg n) ℂ)
    (ps : List (SparsePipelineStep n)) : Matrix (Reg n) (Reg n) ℂ :=
  ps.foldl (fun acc s => sparseStepMatrix rowO colO valO s * acc) 1

/-- Row and column position lists, Gaussian rational entry values, and recorded gate and
arithmetic costs for sparse access. -/
structure SparseOracleData (O I : Type) where

  rowPos : O → List I

  colPos : I → List O

  value : O → I → GaussianRat

  rowCallGates : ℕ

  colCallGates : ℕ

  valueCallGates : ℕ

  arithBits : ℕ

/-- The complex matrix obtained by interpreting the Gaussian rational values of sparse oracle
data. -/
def SparseOracleData.matrix {O I : Type} (d : SparseOracleData O I) : Matrix O I ℂ :=
  fun o i => gaussianRatComplex (d.value o i)

/-- Positive sparsity and entry bounds, duplicate-free position lists of bounded length, and
vanishing values outside the listed row and column positions. -/
def SparseOracleData.IsSparseBounded {O I : Type} (d : SparseOracleData O I)
    (k : ℕ) (b : ℝ) : Prop :=
  0 < k ∧ 0 < b ∧
    (∀ o, (d.rowPos o).length ≤ k ∧ (d.rowPos o).Nodup) ∧
    (∀ i, (d.colPos i).length ≤ k ∧ (d.colPos i).Nodup) ∧
    (∀ o i, i ∉ d.rowPos o → d.value o i = gzero) ∧
    (∀ o i, o ∉ d.colPos i → d.value o i = gzero) ∧
    (∀ o i, ‖gaussianRatComplex (d.value o i)‖ ≤ b)

/-- Accumulate position and value calls, elementary gates, and value-arithmetic costs for a
sparse pipeline. -/
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

/-- A finite matrix description given by dense dyadic entries, a sparse entry list, or a
QRAM-style read function with a recorded read cost. -/
inductive MatrixInputModel where

  | explicit (rows cols : ℕ) (num : Fin rows → Fin cols → ℤ × ℤ) (bits : ℕ)

  | sparse (rows cols : ℕ) (items : List (ℕ × ℕ × ℤ × ℤ)) (bits : ℕ)

  | qram (rows cols : ℕ) (read : ℕ → ℕ → ℤ × ℤ) (bits : ℕ) (readCost : ℕ)

/-- The number of rows declared by a matrix input model. -/
def MatrixInputModel.rows : MatrixInputModel → ℕ
  | .explicit r _ _ _ => r
  | .sparse r _ _ _ => r
  | .qram r _ _ _ _ => r

/-- The number of columns declared by a matrix input model. -/
def MatrixInputModel.cols : MatrixInputModel → ℕ
  | .explicit _ c _ _ => c
  | .sparse _ c _ _ => c
  | .qram _ c _ _ _ => c

/-- Decode the matrix input model, taking the first matching sparse entry and using zero when no
sparse entry matches. -/
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

/-- The recorded bit cost of reading dense, sparse-list, or QRAM-style matrix data. -/
def MatrixInputModel.readBitCost (m : MatrixInputModel) : ℕ :=
  match m with
  | .explicit rows cols _ bits => rows * cols * (2 * (bits + 1))
  | .sparse _ _ items bits => items.length * (2 * (bits + 1) + 4)
  | .qram rows cols _ bits readCost => readCost * rows * cols + rows * cols * (2 * (bits + 1))

/-- Every fixed gate in the circuit is the numerical matrix of some local QFT gate word at
precision `k`. -/
def OnFiniteBackend {N : ℕ} (k : ℕ) (C : Circuit (Reg N)) : Prop :=
  ∀ U : Matrix (Reg N) (Reg N) ℂ, Step.gate U ∈ C →
    ∃ gs : List (LocalQFTGate N), U = numericalProgramMatrix k gs

/-- The accumulated backend error expression `totalLocalGates * 2^(-k)`. -/
noncomputable def finiteBackendErrorBound (k totalLocalGates : ℕ) : ℝ :=
  (totalLocalGates : ℝ) * ((2 : ℝ)⁻¹)^k

/-- Twice the numerical phase squaring count at precision `k`. -/
def numericalPhaseArithBits (k : ℕ) : ℕ := 2 * numericalPhaseSquarings k

end Qatlib.Concepts.LocalMachine.LocalTransport
