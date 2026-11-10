/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.RecordDrivenVariableTimeAlgorithmVari
import Qatlib.Papers.VarTimeAmpAmp10.Estimate.StructuralEstimateCompilationVari
import Qatlib.Papers.VarTimeAmpAmp10.Estimate.EstimateSandwichVari
import Qatlib.Papers.VarTimeAmpAmp10.StopModel.AverageStopTailBoundVari
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.VariableTimeAlgorithmVari
import Qatlib.Papers.VarTimeAmpAmp10.StopModel.VariableTimeModelWellFormedVari
import Qatlib.Papers.VarTimeAmpAmp10.StopModel.CascadePrefixTransportVari
import Qatlib.Concepts.QlsReadoutSpec.WalkQSVT.ApplicationModels
import Qatlib.Papers.VarTimeAmpAmp10.CoherentAA.LowerBoundModels
import Qatlib.Concepts.BitWordCompiler.WordComposition.NativeModels
import Qatlib.Concepts.QlsReadoutSpec.WalkQSVT.SpectralModels
import Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound.GroverCorrectedOracle
import Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound.InitialStatePrepLowerBoundStat
import Qatlib.Concepts.QlsReadoutSpec.BlockPrecond.OptimalCoefficientBlockEncodingStat
import Qatlib.Concepts.QlsReadoutSpec.BlockPrecond.BlockPrecondCorrectedSubgoalStat
import Qatlib.Concepts.LinearLearning.ConcisePipeline.RandomizedCost
import Qatlib.Concepts.QsvtCore.LinearSystems.NearOptimalReciprocal
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean

open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.QlsReadoutSpec.BlockPrecond
open Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound
open Qatlib.Concepts.QsvtCore.LinearSystems
open Qatlib.Concepts.BlockEncoding.Postselection

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Qatlib.Papers.VarTimeAmpAmp10.CoherentAA

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.BitWordCompiler.WordComposition
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
open Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
open Qatlib.Papers.VarTimeAmpAmp10.Estimate
open Qatlib.Papers.VarTimeAmpAmp10.StopModel
open Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open scoped Classical BigOperators ENNReal ComplexOrder Matrix.Norms.L2Operator

def tightLogFactor (Tmax : ℝ) : ℝ := 1 + Real.log (max 1 Tmax)

def tightAccessCost (Tmax Tav psucc : ℝ) : ℝ :=
  let L := tightLogFactor Tmax
  Tmax * Real.sqrt L + Tav * L ^ ((3 : ℝ) / 2) / Real.sqrt psucc

def iteratedLogFactor (p : ℝ) : ℝ := 1 + Real.log (1 + Real.log (1 / max p (1 / 2)))

def adaptiveEstimateBudget (k p q : ℝ) : ℝ :=
  k * iteratedLogFactor p / Real.sqrt (max q p)

def qlsThm3Cost (Csim κ ε : ℝ) : ℝ :=
  Csim * κ * Real.log (κ / ε) ^ 3 / ε ^ 3 * Real.log (1 / ε) ^ 2

def tightAASuccess (δ : ℝ) (m : ℕ) : ℝ :=
  (1 - ((2 * m + 1 : ℝ) ^ 2) * δ / 3) * ((2 * m + 1 : ℝ) ^ 2) * δ

def tightAAWindow (ε : ℝ) : ℝ := Real.pi / (4 * Real.arcsin (Real.sqrt ε)) - 1 / 2

def gainRatio (r r' : ℝ) : ℝ := Real.sqrt r / Real.sqrt r'

def gainRatioProduct (rs rs' : ℕ → ℝ) (i m : ℕ) : ℝ :=
  ∏ j ∈ Finset.Ico i m, gainRatio (rs j) (rs' j)

def lemma3Rhs (pstop_gt psucc : ℝ) : ℝ := 3 * (1 + Real.sqrt (pstop_gt / psucc))

def remainingStopMass (m : ℕ) (pstop : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), if i < j then pstop j else 0

def eq5StageTimeBound (m : ℕ) (rs rs' : ℝ) (Tprev : ℝ) (i : ℕ) : ℝ :=
  (1 + 1 / (3 * (m : ℝ) - 1)) * gainRatio rs rs' * (Tprev + (2 : ℝ) ^ ((i : ℕ) - 1))

def eq6ProductSum (rs rs' : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico 1 (m + 1), gainRatioProduct rs rs' i (m + 1) * (2 : ℝ) ^ ((i : ℕ) - 1)

def hardFamilySolutionNormSq (d : ℕ) : ℝ :=
  (5 * (d : ℝ) ^ 2 - 8 * (d : ℝ) + 4) / (d : ℝ) ^ 2

def hardFamilyPrepBudget (c p : ℝ) : ℝ := c / Real.sqrt p

def nestedStopLegal {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m + 1) → Matrix H H ℂ) (U : ℕ → Matrix H H ℂ) : Prop :=
  (∀ j : Fin (m + 1), IsOrthogonalProjector (P j)) ∧
  P 0 = 0 ∧ P ⟨m, by omega⟩ = 1 ∧
  (∀ j k : Fin (m + 1), j ≤ k → (P k - P j).PosSemidef) ∧
  (∀ j, U j ∈ Matrix.unitaryGroup H ℂ) ∧
  (∀ j : Fin m, U (j.val + 1) * P ⟨j.val, by omega⟩ = P ⟨j.val, by omega⟩)

def stopTimeData (m : ℕ) (p t : Fin m → ℝ) (Tmax Tav : ℝ) : Prop :=
  0 < m ∧ (∀ i, 0 ≤ p i) ∧ (∑ i, p i = 1) ∧
  (∀ i, 0 ≤ t i) ∧ (∀ i, t i ≤ Tmax) ∧ 1 ≤ Tmax ∧
  Tav ^ 2 = ∑ i, p i * (t i) ^ 2

def goodComponentData {H : Type} [Fintype H] [DecidableEq H]
    (good : Finset H) (ψA ψgood : QState H) (psucc : ℝ) : Prop :=
  Normalized ψA ∧ Normalized ψgood ∧ 0 < psucc ∧
  MeasureProb ψA good = psucc ∧
  ((normVec (Collapse ψA good) : ℂ) • stateVector ψgood = stateVector (Collapse ψA good))

structure VtAmpProgram (H : Type) where

  r : ℕ

  word : Word H r

  readout : Finset (Fin r)

def VtAmpProgram.goodVector {H : Type} [Fintype H] [DecidableEq H] (P : VtAmpProgram H)
    (hr : 0 < P.r) (oracles : ℕ → Matrix H H ℂ) (ω : QState H) : QState H :=
  fun h => ∑ k ∈ P.readout, run hr oracles P.word ω (h, k)

def VtAmpProgram.goodMass {H : Type} [Fintype H] [DecidableEq H] (P : VtAmpProgram H)
    (hr : 0 < P.r) (oracles : ℕ → Matrix H H ℂ) (ω : QState H) : ℝ :=
  outputMass (1 : Matrix H H ℂ) P.readout (run hr oracles P.word ω)

def VtAmpProgram.accessTime {H : Type} (P : VtAmpProgram H) (prices : ℕ → ℕ) : ℕ :=
  weightedCost prices P.word

def estimateAccurate (c q qhat : ℝ) : Prop :=
  0 ≤ qhat ∧ (0 < q → |q - qhat| < c * qhat) ∧ (q = 0 → qhat = 0)

def qlsSpectralWindow {I : Type} [Fintype I] (A : Matrix I I ℂ) (κ : ℝ) : Prop :=
  A.IsHermitian ∧ 1 ≤ κ ∧
  (A - (κ : ℂ)⁻¹ • 1).PosSemidef ∧ ((1 : Matrix I I ℂ) - A).PosSemidef

def qlsThm3Input {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (UA UB : Matrix H H ℂ) (L R : Matrix H I ℂ)
    (ω : QState H) (b : QState I) (κ Csim ε : ℝ) : Prop :=
  qlsSpectralWindow A κ ∧ 0 < Csim ∧ 0 < ε ∧ ε < 1 / 4 ∧
  Normalized b ∧ (∃ z : QState I, A *ᵥ z = b) ∧
  ProjectedUnitaryEncoding A UA L R ∧
  UB ∈ Matrix.unitaryGroup H ℂ ∧ UB *ᵥ ω = L *ᵥ b ∧ Normalized ω

structure UniqueEstData (H : Type) where

  r : ℕ

  est : Word H r

  sh : ℝ

  fourierAmp : ℕ

def UniqueEstData.Legal {H : Type} [Fintype H] [DecidableEq H] (d : UniqueEstData H)
    (oracles : ℕ → Matrix H H ℂ) : Prop :=
  legal 2 d.est ∧ 0 ≤ d.sh ∧ d.sh < 1 ∧ 0 < d.fourierAmp ∧
  wordMatrix oracles d.est ∈ Matrix.unitaryGroup (Space H d.r) ℂ

structure VtInterface where

  slots : ℕ

  prices : ℕ → ℕ

  precision : ℕ

structure VtCompiledCircuit where

  wires : ℕ

  gates : List FiniteGateCode

  bitTime : ℕ

  workspace : ℕ

def VtCompiledCircuit.Legal (P : VtCompiledCircuit) : Prop :=
  finiteWordLegal P.wires P.gates = true ∧ (P.gates).length ≤ P.bitTime ∧
  P.wires ≤ P.workspace

def flagReflectionPrice (r : ℕ) : ℝ := 2 * r + 2

def factorTwoWindow (t qhat : ℝ) : Prop := qhat / 2 < t ∧ t < 2 * qhat

def blockPrecondWitnessJ (c κ ε : ℝ) : ℕ := nearOptimalReciprocalJ (2 * c ^ 2 * κ) ε

def blockPrecondWitnessC0 (c κ ε : ℝ) : ℝ := (4 * (blockPrecondWitnessJ c κ ε : ℝ))⁻¹

end Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
