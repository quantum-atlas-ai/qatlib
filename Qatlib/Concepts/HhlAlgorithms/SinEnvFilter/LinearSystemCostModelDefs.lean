/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.QlsHhlDefs
import Qatlib.Concepts.HhlAlgorithms.UniformHHL.UniformHHLFilter
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeHHLConsumers
open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.HhlAlgorithms.Postselection
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram
open Qatlib.Concepts.HhlAlgorithms.UniformHHL
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvFilter

open Matrix Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open scoped Classical BigOperators

noncomputable def sinEnvelopeFirstPowerBudget (d η : ℝ) : ℝ := 21 / (d * η)

noncomputable def uniformQPEGridBudget (d η : ℝ) : ℝ := 4096 / (d ^ 2 * η ^ 4)

noncomputable def nearOptimalKappaEpsBudget (κ ε : ℝ) : ℝ := 21 * κ / ε

structure SinThreeStateFilter where

  d : ℝ

  eta : ℝ

  grid : ℕ

def SinThreeStateFilter.Budgeted (f : SinThreeStateFilter) : Prop :=
  0 < f.d ∧ f.d ≤ 1 / 4 ∧ 0 < f.eta ∧ f.eta ≤ 1 ∧
    sinEnvelopeFirstPowerBudget f.d f.eta ≤ f.grid

noncomputable def quantizeReal (k : ℕ) (t : ℝ) : ℚ :=
  ((Nat.floor ((2 : ℝ) ^ k * t) : ℤ) : ℚ) / ((2 ^ k : ℕ) : ℚ)

noncomputable def quantizeComplex (k : ℕ) (z : ℂ) : ℂ :=
  ((quantizeReal k z.re : ℚ) : ℂ) + ((quantizeReal k z.im : ℚ) : ℂ) * Complex.I

noncomputable def nonHermitianDilation {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
  qlsScaledDilation A

structure NumericBackendLedger where

  phaseGrid : ℕ

  filterRotations : ℕ

  synthCalls : ℕ

  synthGates : ℕ

  dilationWires : ℕ

  quantDigits : ℕ

  gateCount : ℕ

  bitTime : ℕ

  peakSpace : ℕ

def NumericBackendLedger.Complete (L : NumericBackendLedger)
    (f : SinThreeStateFilter) : Prop :=
  f.Budgeted ∧
    L.phaseGrid = f.grid ∧
    L.filterRotations ≤ L.gateCount ∧
    L.synthCalls * L.synthGates ≤ L.gateCount ∧
    L.gateCount ≤ L.bitTime ∧
    1 + L.dilationWires ≤ L.peakSpace ∧
    0 < L.quantDigits

structure IntegerBitBackend where

  wires : ℕ

  word : List FiniteGateCode

  bitTime : ℕ

  peakSpace : ℕ

def IntegerBitBackend.Legal (B : IntegerBitBackend) : Prop :=
  finiteWordLegal B.wires B.word = true ∧
    B.word.length ≤ B.bitTime ∧
    B.wires ≤ B.peakSpace

def IntegerBitBackend.PolyBounded (B : IntegerBitBackend) : Prop :=
  ∃ (c e : ℕ), B.bitTime ≤ c * (B.wires + 1) ^ e ∧ B.peakSpace ≤ c * (B.wires + 1) ^ e

structure HamiltonianBackend where

  access : SparseAccessSystem

  sparsity : ℕ

  synthesis : SparseHamiltonianSynthesis access

  certEig : Fin access.dim → ℝ

  certV : Operator access.dim

  precision : ℕ

def HamiltonianBackend.Complete (B : HamiltonianBackend) : Prop :=
  B.access.Legal B.sparsity ∧
    B.certV ∈ Matrix.unitaryGroup (Fin B.access.dim) ℂ ∧
    continuousHHLMatrix B.certEig B.certV = B.access.data.matrix ∧
    SparseHamiltonianSynthesis.ImplementsAt B.access B.synthesis
      B.certEig B.certV B.precision ∧
    SparseHamiltonianSynthesis.BudgetBounded B.access B.synthesis
      B.sparsity B.precision

structure PaidAccess where

  wires : ℕ

  forward : List FiniteGateCode

  inverseGates : ℕ

  controlledGates : ℕ

  prepGates : ℕ

  prepInverseGates : ℕ

def PaidAccess.Explicit (a : PaidAccess) : Prop :=
  finiteWordLegal a.wires a.forward = true ∧
    (finiteWordAdjoint a.forward).length = a.forward.length ∧
    a.forward.length ≤ a.inverseGates ∧
    a.forward.length ≤ a.controlledGates ∧
    a.prepGates ≤ a.prepInverseGates

def PaidAccess.RoundTrip (a : PaidAccess) : ℕ :=
  2 * a.forward.length

structure FreshRetrySchedule where

  trials : ℕ

  perTrialSuccess : ℝ

  perTrialCost : ℕ

noncomputable def FreshRetrySchedule.jointFailure (s : FreshRetrySchedule) : ℝ :=
  (1 - s.perTrialSuccess) ^ s.trials

def FreshRetrySchedule.totalCost (s : FreshRetrySchedule) : ℕ :=
  s.trials * s.perTrialCost

def freshRetryIsNotAmplification : Prop :=
  ∀ (s : FreshRetrySchedule), 0 < s.trials → 0 ≤ s.perTrialSuccess →
    s.perTrialSuccess < 1 →
    s.totalCost = s.trials * s.perTrialCost ∧
      s.jointFailure = (1 - s.perTrialSuccess) ^ s.trials ∧
      s.perTrialCost ≤ s.totalCost

def uniformWordQueries (M : ℕ) : ℕ := 2 * (M - 1)

def uniformWordGates (M : ℕ) : ℕ := 4 * (M - 1) + 6

def uniformGridChargedAtFullScale : Prop :=
  ∀ (M : ℕ), 2 ≤ M →
    uniformWordQueries M = 2 * (M - 1) ∧
      uniformWordGates M = 4 * (M - 1) + 6 ∧
      uniformWordQueries M ≤ uniformWordGates M

structure EffectivePreparationBackend where

  dim : ℕ

  prep : List FiniteGateCode

  prepInverse : List FiniteGateCode

  access : SparseAccessSystem

  synthesis : SparseHamiltonianSynthesis access

def EffectivePreparationBackend.Complete (B : EffectivePreparationBackend)
    (s k : ℕ) : Prop :=
  finiteWordLegal (qlsBitWidth B.dim) B.prep = true ∧
    finiteWordLegal (qlsBitWidth B.dim) B.prepInverse = true ∧
    (finiteWordAdjoint B.prep).length = B.prep.length ∧
    ∃ hb : HamiltonianBackend, hb.access = B.access ∧ hb.sparsity = s ∧
      hb.precision = k ∧ hb.Complete

structure SystemDecomputation where

  digits : ℕ

def SystemDecomputation.Complete {m n : ℕ} (D : SystemDecomputation)
    (A : Matrix (Fin m) (Fin n) ℂ) : Prop :=
  0 < D.digits ∧
    ∀ i j,
      |(A i j).re - ((quantizeReal D.digits (A i j).re : ℚ) : ℝ)| <
        (1 / 2 : ℝ) ^ D.digits ∧
      |(A i j).im - ((quantizeReal D.digits (A i j).im : ℚ) : ℝ)| <
        (1 / 2 : ℝ) ^ D.digits

end Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
