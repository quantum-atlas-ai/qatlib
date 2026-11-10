/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.PureToMixedConditionalDefs
import Qatlib.Concepts.HhlErrorBridge.FilterStability
import Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeHHLConsumers
import Qatlib.Concepts.HhlAlgorithms.UniformHHL.OffGridSignedHHL
import Qatlib.Concepts.HhlAlgorithms.Postselection.RationalHHLNoiseRetry
import Qatlib.Concepts.CoherentSim.CoherentOAA.Pseudoinverse
import Qatlib.Concepts.LocalMachine.LocalTransport.LeastSquaresOutputSpec
import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Qatlib.Concepts.RandCompile.FairBitSampling.DiamondStabilizationConsumers
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
import Qatlib.Concepts.BlockEncoding.Basic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL
open Qatlib.Concepts.HhlErrorBridge.FilterStability
open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.HhlAlgorithms.Postselection
open Qatlib.Concepts.HhlAlgorithms.UniformHHL
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.BlockEncoding

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvFilter

open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical Matrix.Norms.L2Operator

noncomputable def threeStateWellMass (d θ : ℝ) : ℝ := sinEnvelopeFilterF d θ ^ 2

noncomputable def threeStateIllMass (d θ : ℝ) : ℝ := sinEnvelopeFilterG d θ ^ 2

noncomputable def threeStateSelectedMass (d θ : ℝ) : ℝ := sinEnvelopeFlagMass d θ

noncomputable def threeStateDirectionBound (e x : ℝ) : ℝ := 2 * e / x

structure ThreeStateFilterRun where

  gap : ℝ

  phase : ℝ

  filterError : ℝ

  targetNorm : ℝ

  directionError : ℝ

  gateBudget : ℕ

  bitBudget : ℕ

def threeStateGateBudget (bits k : ℕ) : ℕ := 256 * 16 * (bits + k + 2) ^ 8

def threeStateBitBudget (bits k : ℕ) : ℕ := 4 * (bits + k + 4)

noncomputable def ThreeStateFilterRun.Realizes (run : ThreeStateFilterRun)
    (bits k : ℕ) : Prop :=
  0 < run.gap ∧ 0 ≤ run.filterError ∧ 0 < run.targetNorm ∧
    run.filterError < run.targetNorm ∧
    threeStateSelectedMass run.gap run.phase
      = threeStateWellMass run.gap run.phase + threeStateIllMass run.gap run.phase ∧
    run.directionError = threeStateDirectionBound run.filterError run.targetNorm ∧
    run.gateBudget ≤ threeStateGateBudget bits k ∧
    run.bitBudget ≤ threeStateBitBudget bits k

noncomputable def nearOptimalKernelQueries (d : ℝ) (k : ℕ) : ℕ :=
  (Nat.ceil (1 / d)) * (8 * k + 16)

structure QpeKernelProgram where

  grid : ℕ

  queryBudget : ℕ

  accuracy : ℝ

def QpeKernelProgram.SolvesAt (K : QpeKernelProgram) (d : ℝ) (k : ℕ) : Prop :=
  2 ≤ K.grid ∧ 0 < K.accuracy ∧
    K.accuracy ≤ uniformHHLAccuracy d k ∧
    K.queryBudget ≤ nearOptimalKernelQueries d k

def finEmbed (N w : ℕ) : Fin N → Reg w := fun i t => i.val.testBit t.1

noncomputable def wordMatrix (w : ℕ) (gs : List FiniteGateCode) :
    Matrix (Reg w) (Reg w) ℂ :=
  (gs.map (finiteCodeMatrix w)).reverse.prod

noncomputable def compressEmbed {I : Type} [Fintype I] {w : ℕ}
    (e : I → Reg w) (G : Matrix (Reg w) (Reg w) ℂ) : Matrix I I ℂ :=
  Matrix.of fun i j => G (e i) (e j)

structure HamiltonianSynthesis (N : ℕ) where

  ham : Matrix (Fin N) (Fin N) ℂ

  time : ℝ

  wires : ℕ

  word : List FiniteGateCode

  error : ℝ

  gateBudget : ℕ

  bitBudget : ℕ

def hamiltonianGateBudget (N bits k : ℕ) : ℕ :=
  256 * (N + 1) ^ 2 * 4 ^ N * (bits + k + 2) ^ 8

def hamiltonianBitBudget (N bits k : ℕ) : ℕ := (N + 2) * (bits + k + 4)

noncomputable def HamiltonianSynthesis.SynthesizesAt {N : ℕ}
    (S : HamiltonianSynthesis N) (bits k : ℕ) : Prop :=
  S.ham.IsHermitian ∧ ‖S.ham‖ ≤ 1 ∧ N ≤ 2 ^ S.wires ∧
    finiteWordLegal S.wires S.word = true ∧
    S.error ≤ (1 / 2 : ℝ) ^ k ∧
    ‖compressEmbed (finEmbed N S.wires) (wordMatrix S.wires S.word)
      - HamiltonianEvolution S.ham S.time‖ ≤ S.error ∧
    S.gateBudget ≤ hamiltonianGateBudget N bits k ∧
    S.bitBudget ≤ hamiltonianBitBudget N bits k

noncomputable def dyadicRound (x : ℝ) (k : ℕ) : ℝ :=
  (Int.floor ((2 : ℝ) ^ k * x) : ℝ) / (2 : ℝ) ^ k

structure RealInputQuantizer where

  digits : ℕ

def RealInputQuantizer.QuantizesAt (Q : RealInputQuantizer)
    (x y : ℝ) : Prop :=
  y = dyadicRound x Q.digits ∧ 0 < Q.digits

structure HhlBackendLedger where

  elementaryGates : ℕ

  integerBits : ℕ

  peakSpaceBits : ℕ

def hhlBackendBudget (wires bits k : ℕ) : HhlBackendLedger :=
  ⟨256 * (wires + 1) ^ 2 * 4 ^ wires * (bits + k + 2) ^ 8,
    (wires + 2) * (bits + k + 4),
    (wires + 2) * (bits + k + 4)⟩

structure InstrumentAccessCost where

  measurementAccesses : ℕ

  preparationAccesses : ℕ

  inverseAccesses : ℕ

def instrumentAccessBudget (calls : ℕ) : InstrumentAccessCost :=
  ⟨calls, calls + 1, calls⟩

noncomputable def successorSuccessGap (d θ : ℝ) : ℝ := ((d * θ) / 2) ^ 2

def successorTightParam (d θ : ℚ) (k : ℕ) : ℚ := numericHHLAccuracy d θ k

def successorGateBudget (calls bits k : ℕ) : ℕ :=
  256 * (calls + 1) ^ 2 * (bits + k + 2) ^ 8

def successorBitBudget (calls bits k : ℕ) : ℕ := (calls + 2) * (bits + k + 4)

structure SuccessorProgramBudget where

  successGap : ℝ

  tightParam : ℝ

  access : InstrumentAccessCost

  gateBudget : ℕ

  bitBudget : ℕ

def SuccessorProgramBudget.Realizes (B : SuccessorProgramBudget)
    (calls bits k : ℕ) : Prop :=
  0 < B.successGap ∧ B.successGap ≤ 1 ∧ 0 < B.tightParam ∧
    B.access.measurementAccesses ≤ (instrumentAccessBudget calls).measurementAccesses ∧
    B.access.preparationAccesses ≤ (instrumentAccessBudget calls).preparationAccesses ∧
    B.access.inverseAccesses ≤ (instrumentAccessBudget calls).inverseAccesses ∧
    B.gateBudget ≤ successorGateBudget calls bits k ∧
    B.bitBudget ≤ successorBitBudget calls bits k

end Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
