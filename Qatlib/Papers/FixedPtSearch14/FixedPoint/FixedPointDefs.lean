/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL
import Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeHHLConsumers
import Qatlib.Concepts.MbqcFlow.FlowDecision.PureToMixedConditional
import Qatlib.Concepts.TensorRegisters.RegisterModel.RegisterMeasurement
import Qatlib.Concepts.BlockEncoding.Postselection
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.NativeAeReadout
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.NativeAeReadoutConsumers
import Qatlib.Concepts.SdpDuality.ConeSeparation.MeasurementStatistics
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.MonteCarloMean.LayeredMean.LayeredQuantumMean
import Qatlib.Concepts.MonteCarloMean.PilotVariance.PilotQuantumMeanConsumers
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL
open Qatlib.Concepts.HhlErrorBridge.FilterStability

set_option autoImplicit false

namespace Qatlib.Papers.FixedPtSearch14.FixedPoint

open Matrix Qatlib
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

def sinEnvelopeNothingFlag : Fin 3 := 0

def sinEnvelopeWellFlag : Fin 3 := 1

def sinEnvelopeIllFlag : Fin 3 := 2

def sinEnvelopeWellEvent : Finset (Fin 3) := {sinEnvelopeWellFlag}

def sinEnvelopeIllEvent : Finset (Fin 3) := {sinEnvelopeIllFlag}

noncomputable def sinEnvelopeFilterInstrument (d θ : ℝ) (hd : 0 < d) :
    Instrument Bool 3 3 :=
  basisEventInstrument (sinEnvelopeFlagRotation d θ)
    (sin_envelope_flag_rotation_unitary_and_column d θ hd).1 sinEnvelopeWellEvent

noncomputable def sinEnvelopeActualWellMass (d θ : ℝ) (hd : 0 < d) : ℝ :=
  instrumentProb (sinEnvelopeFilterInstrument d θ hd) (outerProduct (Ket (0 : Fin 3))) true

noncomputable def sinEnvelopeIdealWellMass (d θ : ℝ) : ℝ :=
  (sinEnvelopeFilterF d θ) ^ 2

noncomputable def sinEnvelopeIdealIllMass (d θ : ℝ) : ℝ :=
  (sinEnvelopeFilterG d θ) ^ 2

noncomputable def sinEnvelopeActualWellOutput (d θ : ℝ) (hd : 0 < d) :
    Option (QState (Fin 3)) :=
  ProjectiveConditionalState (Projector sinEnvelopeWellEvent) true
    (ApplyGate (sinEnvelopeFlagRotation d θ) (Ket (0 : Fin 3)))

noncomputable def sinEnvelopeActualWellVector (d θ : ℝ) (hd : 0 < d) : QState (Fin 3) :=
  Collapse (ApplyGate (sinEnvelopeFlagRotation d θ) (Ket (0 : Fin 3)))
    sinEnvelopeWellEvent

structure SinEnvelopeFilterExecution (d θ : ℝ) where

  rotation : Matrix (Fin 3) (Fin 3) ℂ

  error : ℝ

  error_nonneg : 0 ≤ error

  error_le : ‖rotation - sinEnvelopeFlagRotation d θ‖ ≤ error

  threshold_pos : 0 < d

noncomputable def SinEnvelopeFilterExecution.wellVector {d θ : ℝ}
    (E : SinEnvelopeFilterExecution d θ) : QState (Fin 3) :=
  Collapse (E.rotation *ᵥ Ket (0 : Fin 3)) sinEnvelopeWellEvent

noncomputable def SinEnvelopeFilterExecution.wellMass {d θ : ℝ}
    (E : SinEnvelopeFilterExecution d θ) : ℝ :=
  MeasureProb (E.rotation *ᵥ Ket (0 : Fin 3)) sinEnvelopeWellEvent

structure ConditionalChannelProgram (O : Type) [Fintype O] (D E : ℕ) where

  actual : Instrument O D E

  ideal : Instrument O D E

  selected : Finset O

  error : ℝ

  gap : ℝ

  pureCertificate : PureUniformBranchBound actual ideal selected error gap

inductive SuccessorCaller

  | hhl

  | amplitudeEstimation

  | statistics
  deriving DecidableEq, Repr

structure CallerAccessLedger where

  oracleAccesses : ℕ

  macroGateAccesses : ℕ
  deriving DecidableEq, Repr

structure CallerAccessBudget where

  oracle : ℕ

  macroGates : ℕ
  deriving DecidableEq, Repr

def CallerAccessLedger.withinBudget (l : CallerAccessLedger) (b : CallerAccessBudget) : Prop :=
  l.oracleAccesses ≤ b.oracle ∧ l.macroGateAccesses ≤ b.macroGates

noncomputable def callerSuccessGap : SuccessorCaller → ℝ
  | .hhl => 1 / 4
  | .amplitudeEstimation => 8 / Real.pi ^ 2
  | .statistics => 1 - (8 / 9 : ℝ)

noncomputable def hhlCallerLedger (M : ℕ) : CallerAccessLedger :=
  ⟨2 * (M - 1), 4 * (M - 1) + 6⟩

noncomputable def aeCallerLedger (M : ℕ) : CallerAccessLedger :=
  ⟨2 * (M - 1) + 1 + (M - 1), 2 * (M - 1) + 2⟩

noncomputable def statisticsCallerLedger (M r : ℕ) : CallerAccessLedger :=
  ⟨(2 * r + 1) * (M - 1), (2 * r + 1) * (5 * (M - 1) + 3)⟩

end Qatlib.Papers.FixedPtSearch14.FixedPoint
