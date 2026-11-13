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

/-!
# Filter branches and consumer resource records

This module defines the three-state sine-envelope flag interface, its well-branch instrument,
and the associated branch masses and conditional vectors. `SinEnvelopeFilterExecution` records
an approximate rotation with an operator-norm error certificate, while
`ConditionalChannelProgram` stores a uniform pure-state branch certificate for actual and ideal
instruments.

The caller types and resource ledgers provide interfaces for HHL, amplitude-estimation, and
statistics consumers in the fixed-point search development associated with [YoderLowChuang2014].

## Main definitions

* `sinEnvelopeFilterInstrument`: the Boolean well-event instrument.
* `SinEnvelopeFilterExecution`: an approximate rotation and its error bound.
* `ConditionalChannelProgram`: instruments with a selected-branch certificate.
* `CallerAccessLedger`: oracle and macro-gate resource counts.

## References

* [Yoder et al., 2014][YoderLowChuang2014]
-/

set_option backward.isDefEq.respectTransparency false
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

/-- The flag value zero representing the initial or unclassified filter outcome. -/
def sinEnvelopeNothingFlag : Fin 3 := 0

/-- The flag value one representing the well branch of the sine-envelope filter. -/
def sinEnvelopeWellFlag : Fin 3 := 1

/-- The flag value two representing the ill branch of the sine-envelope filter. -/
def sinEnvelopeIllFlag : Fin 3 := 2

/-- The singleton event containing the well flag. -/
def sinEnvelopeWellEvent : Finset (Fin 3) := {sinEnvelopeWellFlag}

/-- The singleton event containing the ill flag. -/
def sinEnvelopeIllEvent : Finset (Fin 3) := {sinEnvelopeIllFlag}

/-- The Boolean instrument obtained by applying the sine-envelope flag rotation and measuring
whether the well event occurs. -/
noncomputable def sinEnvelopeFilterInstrument (d θ : ℝ) (hd : 0 < d) :
    Instrument Bool 3 3 :=
  basisEventInstrument (sinEnvelopeFlagRotation d θ)
    (sin_envelope_flag_rotation_unitary_and_column d θ hd).1 sinEnvelopeWellEvent

/-- The probability of the well outcome for the filter instrument initialized in the flag-zero
pure state. -/
noncomputable def sinEnvelopeActualWellMass (d θ : ℝ) (hd : 0 < d) : ℝ :=
  instrumentProb (sinEnvelopeFilterInstrument d θ hd) (outerProduct (Ket (0 : Fin 3))) true

/-- The ideal well mass, defined as the square of `sinEnvelopeFilterF d θ`. -/
noncomputable def sinEnvelopeIdealWellMass (d θ : ℝ) : ℝ :=
  (sinEnvelopeFilterF d θ) ^ 2

/-- The ideal ill mass, defined as the square of `sinEnvelopeFilterG d θ`. -/
noncomputable def sinEnvelopeIdealIllMass (d θ : ℝ) : ℝ :=
  (sinEnvelopeFilterG d θ) ^ 2

/-- The optional conditional pure state obtained by selecting the well event after rotating the
flag-zero state. -/
noncomputable def sinEnvelopeActualWellOutput (d θ : ℝ) (hd : 0 < d) :
    Option (QState (Fin 3)) :=
  ProjectiveConditionalState (Projector sinEnvelopeWellEvent) true
    (ApplyGate (sinEnvelopeFlagRotation d θ) (Ket (0 : Fin 3)))

/-- The unnormalized well-branch vector obtained by collapsing the rotated flag-zero state onto
the well event. -/
noncomputable def sinEnvelopeActualWellVector (d θ : ℝ) (hd : 0 < d) : QState (Fin 3) :=
  Collapse (ApplyGate (sinEnvelopeFlagRotation d θ) (Ket (0 : Fin 3)))
    sinEnvelopeWellEvent

/-- An approximate flag rotation equipped with a nonnegative operator-norm error bound relative
to the sine-envelope rotation and a positive threshold. -/
structure SinEnvelopeFilterExecution (d θ : ℝ) where

  rotation : Matrix (Fin 3) (Fin 3) ℂ

  error : ℝ

  error_nonneg : 0 ≤ error

  error_le : ‖rotation - sinEnvelopeFlagRotation d θ‖ ≤ error

  threshold_pos : 0 < d

/-- The unnormalized well-branch vector produced by the execution's rotation on the flag-zero
state. -/
noncomputable def SinEnvelopeFilterExecution.wellVector {d θ : ℝ}
    (E : SinEnvelopeFilterExecution d θ) : QState (Fin 3) :=
  Collapse (E.rotation *ᵥ Ket (0 : Fin 3)) sinEnvelopeWellEvent

/-- The well-event measurement mass of the execution's rotated flag-zero state. -/
noncomputable def SinEnvelopeFilterExecution.wellMass {d θ : ℝ}
    (E : SinEnvelopeFilterExecution d θ) : ℝ :=
  MeasureProb (E.rotation *ᵥ Ket (0 : Fin 3)) sinEnvelopeWellEvent

/-- Actual and ideal instruments with selected outcomes, error and gap parameters, and a uniform
pure-state branch certificate. -/
structure ConditionalChannelProgram (O : Type) [Fintype O] (D E : ℕ) where

  actual : Instrument O D E

  ideal : Instrument O D E

  selected : Finset O

  error : ℝ

  gap : ℝ

  pureCertificate : PureUniformBranchBound actual ideal selected error gap

/-- The three consumer categories: HHL, amplitude estimation, and statistics. -/
inductive SuccessorCaller

  | hhl

  | amplitudeEstimation

  | statistics
  deriving DecidableEq, Repr

/-- A resource record containing oracle-access and macro-gate-access counts. -/
structure CallerAccessLedger where

  oracleAccesses : ℕ

  macroGateAccesses : ℕ
  deriving DecidableEq, Repr

/-- Upper budgets for oracle accesses and macro-gate accesses. -/
structure CallerAccessBudget where

  oracle : ℕ

  macroGates : ℕ
  deriving DecidableEq, Repr

/-- The proposition that both counts in an access ledger are bounded by the corresponding
resource budgets. -/
def CallerAccessLedger.withinBudget (l : CallerAccessLedger) (b : CallerAccessBudget) : Prop :=
  l.oracleAccesses ≤ b.oracle ∧ l.macroGateAccesses ≤ b.macroGates

/-- The designated success gaps `1 / 4`, `8 / Real.pi ^ 2`, and `1 - 8 / 9` for HHL, amplitude
estimation, and statistics, respectively. -/
noncomputable def callerSuccessGap : SuccessorCaller → ℝ
  | .hhl => 1 / 4
  | .amplitudeEstimation => 8 / Real.pi ^ 2
  | .statistics => 1 - (8 / 9 : ℝ)

/-- The HHL caller ledger with `2 * (M - 1)` oracle accesses and `4 * (M - 1) + 6` macro-gate
accesses. -/
noncomputable def hhlCallerLedger (M : ℕ) : CallerAccessLedger :=
  ⟨2 * (M - 1), 4 * (M - 1) + 6⟩

/-- The amplitude-estimation caller ledger with `2 * (M - 1) + 1 + (M - 1)` oracle accesses and
`2 * (M - 1) + 2` macro-gate accesses. -/
noncomputable def aeCallerLedger (M : ℕ) : CallerAccessLedger :=
  ⟨2 * (M - 1) + 1 + (M - 1), 2 * (M - 1) + 2⟩

/-- The statistics caller ledger with `(2 * r + 1) * (M - 1)` oracle accesses and `(2 * r + 1) *
(5 * (M - 1) + 3)` macro-gate accesses. -/
noncomputable def statisticsCallerLedger (M r : ℕ) : CallerAccessLedger :=
  ⟨(2 * r + 1) * (M - 1), (2 * r + 1) * (5 * (M - 1) + 3)⟩

end Qatlib.Papers.FixedPtSearch14.FixedPoint
