/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralFilter.PhaseReadout.PhaseEstimation
import Qatlib.Concepts.IntWordFraming.WordFraming.FourierRecovery
import Qatlib.Concepts.IntWordFraming.WordFraming.SmithNormalizationDefs
import Qatlib.Concepts.IntWordFraming.WordFraming.SmithFramingDefs
import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGAdder
import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGMultiplier
import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGDivider
import Qatlib.Concepts.RiskEstimation.PolyRotation.PolyControlledRotationCorrected
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
import Qatlib.Concepts.QftPreparation.LocalQFTImplementation
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.LocalQFTReadout
import Qatlib.Concepts.HspRecovery.CyclicRecovery.CyclicPeriodSampling
import Qatlib.Concepts.HspRecovery.Distinguisher.HiddenSubgroupSampling
import Qatlib.Concepts.HspRecovery.AbelianSampling.AbelianStabilizerGenerationSubgoalQuan
import Qatlib.Concepts.PeriodSampling.OrderRecovery.BoundedRationalOrderDecoder
import Qatlib.Concepts.RiskEstimation.PopulationGap.OrderShorDefs
import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.OrderShor
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedVariables false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.RiskEstimation.PolyRotation
open Qatlib.Concepts.PeriodSampling.OrderRecovery
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation Qatlib.Concepts.CircuitImpl.ReflectionCompile
open Qatlib.Concepts.MatrixAccess.RitzPipeline

namespace Qatlib.Concepts.HspRecovery.AbelianSampling

open Qatlib
open Qatlib.Concepts.IntWordFraming.WordFraming
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib
open Qatlib.Concepts.HspRecovery.Distinguisher
open Qatlib
open Qatlib
open Qatlib.Concepts.RiskEstimation.PopulationGap
open Qatlib.Concepts.PeriodSampling.FactorAlgorithm
open Qatlib.Concepts.HspRecovery.AbelianSampling
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.StabilizerAlg.NearUniformGen
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder Classical

def stageA_fourier_recovery_clause1_spec : Prop :=
  (∀ {C : Type} [AddCommGroup C] {m n m' n' : ℕ}
    (p : CompactAbelianPresentation C m n) (q : CompactAbelianPresentation C m' n'),
    p.Valid → q.Valid → Finite C → p.run.factors = q.run.factors) ∧
  (∀ {C : Type} [AddCommGroup C] {m n : ℕ} (p : CompactAbelianPresentation C m n)
    (hp : p.Valid) (v : Fin m → ℤ),
    compactRecoveryEquiv p hp (generatorWordMap p.generators v) = normalizedEncode p.run v) ∧
  (∀ {C : Type} [AddCommGroup C] {m n : ℕ} (p : CompactAbelianPresentation C m n)
    (hp : p.Valid) (u v : Fin m → ℤ),
    normalizedWordEq p.run u v = true ↔ generatorWordMap p.generators u = generatorWordMap p.generators v) ∧
  (∀ {C : Type} [AddCommGroup C] {m n : ℕ} (p : CompactAbelianPresentation C m n)
    (hp : p.Valid) (r : Fin m),
    compactRecoveryEquiv p hp (generatorWordMap p.generators (fun i => p.run.reduction.leftInverse i r)) =
      fun s : {i : Fin m // p.run.coeff i ≠ 1} => if (s : Fin m) = r then (1 : ZMod (p.run.coeff s)) else 0) ∧
  (∀ {m n m' n' : ℕ} (rows : Vector (Vector SmithIntegerCode n) m)
    (rows' : Vector (Vector SmithIntegerCode n') m'),
    (smithRunBinaryEuclid rows).1.1.isFinite = true →
    ∀ (e : PresentationModule (tableMatrix (smithDecodeRelations rows)) ≃+
      PresentationModule (tableMatrix (smithDecodeRelations rows'))),
      (smithRunBinaryEuclid rows).1.1.factors = (smithRunBinaryEuclid rows').1.1.factors) ∧
  (∀ {m n : ℕ} (rows : Vector (Vector SmithIntegerCode n) m) (op : SmithKernelOp),
    (smithRunBinaryEuclid rows).1.2 op ≤
      smithRectangularBudget m n ((smithRunBinaryEuclid rows).1.2 .pivotFuelAllocated) op) ∧
  (∀ {m n : ℕ} (rows : Vector (Vector SmithIntegerCode n) m),
    (smithRunBinaryEuclid rows).2.quotRemPairs ≤
      (m + n) * (smithRunBinaryEuclid rows).1.2 .pivotFuelAllocated *
        (2 * (smithRunBinaryEuclid rows).2.peakPairInputBits + 2)) ∧
  (∀ {M : ℕ} {I : Type} [Fintype I] [DecidableEq I] (hM : 0 < M)
    {U : Matrix I I ℂ} {ψ : QState I} (hψn : Normalized ψ) (j : Fin M),
    U.mulVec ψ = (primRoot M ^ ((j.val : ℤ))) • ψ →
    ApplyGate (TensorGate (QFTMatrix M).conjTranspose 1)
        ((ControlledPowers U M).mulVec (TensorState (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) ψ))
      = TensorState (Ket j) ψ ∧
    MeasureProb (ApplyGate (TensorGate (QFTMatrix M).conjTranspose 1)
        ((ControlledPowers U M).mulVec (TensorState (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) ψ)))
        ({j} ×ˢ (Finset.univ : Finset I)) = 1)

def stageA_fourier_recovery_clause2_spec : Prop :=
  (∀ (w : ℕ),
    reflectionLegal (booleanDAGSteps (booleanWordAdderDAG w) (booleanWordAdderSelect w)) ∧
    (booleanDAGSteps (booleanWordAdderDAG w) (booleanWordAdderSelect w)).length ≤ 151 * w + 31 ∧
    QueryCount (reflectionCompile (booleanDAGSteps (booleanWordAdderDAG w) (booleanWordAdderSelect w))) = 0 ∧
    GateCount (reflectionCompile (booleanDAGSteps (booleanWordAdderDAG w) (booleanWordAdderSelect w))) =
      (booleanDAGSteps (booleanWordAdderDAG w) (booleanWordAdderSelect w)).length) ∧
  (∀ (w : ℕ) (ψ : QState (Reg (2 * w) × Reg (w + 1))),
    Run (1 : Matrix (Reg ((2 * w) + (5 * w + 1) + (w + 1))) (Reg ((2 * w) + (5 * w + 1) + (w + 1))) ℂ)
      (reflectionCompile (booleanDAGSteps (booleanWordAdderDAG w) (booleanWordAdderSelect w)))
      (booleanDAGEmbed (2 * w) (5 * w + 1) (w + 1) ψ) =
      ∑ xy, ψ xy • Ket (booleanDAGInput (2 * w) (5 * w + 1) (w + 1) xy.1
        (fun j => xy.2 j ^^ booleanWordAdderResult w
          (booleanWordAdderLeft w xy.1) (booleanWordAdderRight w xy.1) j))) ∧
  (∀ (w : ℕ) (a b : Reg w) (y : Reg (2 * w)),
    let p := booleanWordMulProgram w
    Run (1 : Matrix (Reg (2 * w + p.nodes + 2 * w)) (Reg (2 * w + p.nodes + 2 * w)) ℂ)
      (reflectionCompile (booleanDAGSteps p.graph (booleanWordMulSelect w)))
      (Ket (booleanDAGInput (2 * w) p.nodes (2 * w) (booleanWordAdderInput w a b) y)) =
      Ket (booleanDAGInput (2 * w) p.nodes (2 * w) (booleanWordAdderInput w a b)
        (fun j => y j ^^ booleanWordMulResult w a b j))) ∧
  (∀ (w : ℕ) (ψ : QState (Reg (2 * w) × Reg (2 * w))),
    let p := booleanWordMulProgram w
    Run (1 : Matrix (Reg (2 * w + p.nodes + 2 * w)) (Reg (2 * w + p.nodes + 2 * w)) ℂ)
      (reflectionCompile (booleanDAGSteps p.graph (booleanWordMulSelect w)))
      (booleanDAGEmbed (2 * w) p.nodes (2 * w) ψ) =
      ∑ xy, ψ xy • Ket (booleanDAGInput (2 * w) p.nodes (2 * w) xy.1
        (fun j => xy.2 j ^^ booleanWordMulResult w
          (booleanWordAdderLeft w xy.1) (booleanWordAdderRight w xy.1) j))) ∧
  (∀ (w : ℕ) (a b : Reg w),
    booleanWordLSBValue w (booleanWordDivQuotient w a b) = booleanWordLSBValue w a / booleanWordLSBValue w b ∧
    booleanWordLSBValue (2 * w) (booleanWordDivRemainder w a b) = booleanWordLSBValue w a % booleanWordLSBValue w b) ∧
  (∀ {N : ℕ} (S ws : List (Fin N)),
    S.length - 1 ≤ ws.length → (subsetActiveWorks S ws).length = S.length - 1) ∧
  (∀ (n : ℕ) (g : FiniteGateCode), finiteCodeLegal n g = true → finiteCodeMatrix n g ∈ Matrix.unitaryGroup (Reg n) ℂ) ∧
  (∀ (n : ℕ),
    GateCount (localProgramCircuit (localQFT n)) = n + n * (n - 1) / 2 + n / 2 ∧
    QueryCount (localProgramCircuit (localQFT n)) = 0) ∧
  (∀ (n b : ℕ),
    GateCount (localProgramCircuit (approxLocalQFT n b)) ≤ n + n * (b + 1) + n / 2) ∧
  (∀ (n b : ℕ) (ψ : QState (Reg n)) (S : Finset (Reg n)),
    Normalized ψ →
    |MeasureProb (Run 1 (localProgramCircuit (approxLocalQFT n b)) ψ) S -
        MeasureProb (ApplyGate (relabelGate (bitVecEquiv n).symm (QFTMatrix (2 ^ n))) ψ) S| ≤
      Real.pi * (n : ℝ) / (2 : ℝ) ^ b ∧
    |MeasureProb (Run 1 (localProgramCircuit (localProgramAdjoint (approxLocalQFT n b))) ψ) S -
        MeasureProb (ApplyGate (relabelGate (bitVecEquiv n).symm (QFTMatrix (2 ^ n))).conjTranspose ψ) S| ≤
      Real.pi * (n : ℝ) / (2 : ℝ) ^ b) ∧
  (∀ {M : ℕ} {I : Type} [Fintype I] [DecidableEq I] (hM : 0 < M)
    {U : Matrix I I ℂ} {ψ : QState I} (hψn : Normalized ψ) (j : Fin M),
    U.mulVec ψ = (primRoot M ^ ((j.val : ℤ))) • ψ →
    ApplyGate (TensorGate (QFTMatrix M).conjTranspose 1)
        ((ControlledPowers U M).mulVec (TensorState (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) ψ))
      = TensorState (Ket j) ψ ∧
    MeasureProb (ApplyGate (TensorGate (QFTMatrix M).conjTranspose 1)
        ((ControlledPowers U M).mulVec (TensorState (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) ψ)))
        ({j} ×ˢ (Finset.univ : Finset I)) = 1)

def stageA_fourier_recovery_clause3_spec : Prop :=
  (∀ {R : Type} [Fintype R] [DecidableEq R] [AddCommGroup R]
    (N : ℕ) (hN : 0 < N) (f : Fin N → R),
    QueryCount (cyclicSamplingCircuit (R := R) N) = 1 ∧
    GateCount (cyclicSamplingCircuit (R := R) N) = 2 ∧
    IsUnitaryCircuit (cyclicSamplingCircuit (R := R) N) ∧
    (∀ y : Fin N, (cyclicSampleDist N hN f).prob y =
      MarginalProbLeft (Run (AddOracle f) (cyclicSamplingCircuit (R := R) N)
        (TensorState (Ket ⟨0, hN⟩) (Ket 0))) {y})) ∧
  (∀ {R : Type} [Fintype R] [DecidableEq R] [AddCommGroup R]
    (N r : ℕ) (hN : 0 < N) (f : Fin N → R),
    0 < r → r ∣ N →
    (∀ x y : Fin N, f x = f y ↔ (x.val : ℕ) % r = (y.val : ℕ) % r) →
    ∀ y : Fin N, (cyclicSampleDist N hN f).prob y = if (N / r) ∣ y.val then 1 / (r : ℝ) else 0) ∧
  (∀ {G R : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup R] [Fintype R] [DecidableEq R] (e : G ≃ AddChar G ℂ),
    QueryCount (hiddenSubgroupSamplingCircuit (R := R) e) = 1 ∧
    GateCount (hiddenSubgroupSamplingCircuit (R := R) e) = 1 ∧
    Size (hiddenSubgroupSamplingCircuit (R := R) e) = 2) ∧
  (∀ {G R : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup R] [Fintype R] [DecidableEq R]
    (f : G → R) (e : G ≃ AddChar G ℂ) (E : Finset G) (P : Matrix (G × R) (G × R) ℂ) (δ : ℝ),
    P ∈ Matrix.unitaryGroup (G × R) ℂ →
    ‖AddOracle f - P‖ ≤ δ →
    |MarginalProbLeft (Run (AddOracle f) (hiddenSubgroupSamplingCircuit (R := R) e)
        (TensorState (Uniform G) (Ket 0))) E -
      MarginalProbLeft (Run P (hiddenSubgroupSamplingCircuit (R := R) e)
        (TensorState (Uniform G) (Ket 0))) E| ≤ 2 * δ) ∧
  AbelianStabilizerGenerationSubgoal ∧
  (∀ (M y : ℕ) (cs : List (ℕ × ℕ)), (boundedRationalScan M y cs).2 ≤ cs.length) ∧
  (∀ (M y : ℕ) (cs : List (ℕ × ℕ)) (c : ℕ × ℕ),
    (boundedRationalScan M y cs).1 = some c → c ∈ cs ∧ boundedRationalAccept M y c = true) ∧
  (∀ {M : ℕ} {I : Type} [Fintype I] [DecidableEq I] (hM : 0 < M)
    {U : Matrix I I ℂ} {ψ : QState I} (hψn : Normalized ψ) (j : Fin M),
    U.mulVec ψ = (primRoot M ^ ((j.val : ℤ))) • ψ →
    ApplyGate (TensorGate (QFTMatrix M).conjTranspose 1)
        ((ControlledPowers U M).mulVec (TensorState (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) ψ))
      = TensorState (Ket j) ψ ∧
    MeasureProb (ApplyGate (TensorGate (QFTMatrix M).conjTranspose 1)
        ((ControlledPowers U M).mulVec (TensorState (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) ψ)))
        ({j} ×ˢ (Finset.univ : Finset I)) = 1)

def modMulGate {n : ℕ} (c : ZMod n) (b : Bool) : ZMod n → ZMod n :=
  fun x => if b then c * x else x

def modeExpSchedule {n : ℕ} (a : ZMod n) : List Bool → ℕ → List (ZMod n × Bool)
  | [], _ => []
  | b :: bs, k => (a ^ 2 ^ k, b) :: modeExpSchedule a bs (k + 1)

def modeExpWord {n : ℕ} (a : ZMod n) (e : ℕ) : List (ZMod n → ZMod n) :=
  (modeExpSchedule a (modExpBits e) 0).map (fun p => modMulGate p.1 p.2)

def applyModWord {n : ℕ} (w : List (ZMod n → ZMod n)) (x : ZMod n) : ZMod n :=
  w.foldl (fun acc g => g acc) x

def StageAFourierRecoveryClause2ModeExpEndpoint : Prop :=
  (∀ (n a e : ℕ) (x : ZMod n),
    applyModWord (modeExpWord (a : ZMod n) e) x = x * (a : ZMod n) ^ e) ∧
  (∀ (n a e : ℕ), IsUnit (a : ZMod n) →
    Function.Bijective (applyModWord (modeExpWord (a : ZMod n) e))) ∧
  (∀ (n a e : ℕ), (modeExpWord (a : ZMod n) e).length = (modExpBits e).length) ∧
  (∀ (n a e : ℕ),
    ((modeExpSchedule (a : ZMod n) (modExpBits e) 0).map (fun p => p.2)).count true
      = (modExpBits e).count true) ∧
  (∀ (n a e : ℕ) (hn : 0 < n),
    applyModWord (modeExpWord (a : ZMod n) e) 1 = (modExpResult n a e : ZMod n))

end Qatlib.Concepts.HspRecovery.AbelianSampling
