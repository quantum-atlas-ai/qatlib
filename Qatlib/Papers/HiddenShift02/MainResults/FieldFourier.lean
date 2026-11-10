/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.NativeNumerics.NumericalQFT
import Qatlib.Concepts.QftPreparation.LocalQft
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation
open Qatlib.Concepts.NativeNumerics.NumericalQFT
open Qatlib.Concepts.QftPreparation.LocalQft
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.HiddenShift02.MainResults.FieldFourier

open Matrix

theorem source_lemma2_exact (n : ℕ) :
    localProgramMatrix (localQFT n) =
        relabelGate (bitVecEquiv n).symm (QFTMatrix (2 ^ n)) ∧
      GateCount (localProgramCircuit (localQFT n)) = n + n * (n - 1) / 2 + n / 2 ∧
      QueryCount (localProgramCircuit (localQFT n)) = 0 :=
  Qatlib.Concepts.QftPreparation.LocalQft.aqLocalQFT_actual_matrix_and_cost n

theorem source_lemma2 (n t : ℕ) (ψ : QState (Reg n)) (S : Finset (Reg n))
    (hψ : Normalized ψ) :
    |MeasureProb (Run (1 : Matrix (Reg n) (Reg n) ℂ)
          (numericalDyadicCircuit (numericalPhaseBudget n t) (localQFT n)) ψ) S
        - MeasureProb (ApplyGate (relabelGate (bitVecEquiv n).symm (QFTMatrix (2 ^ n))) ψ) S|
        ≤ ((2 : ℝ) ⁻¹) ^ t ∧
      GateCount (numericalDyadicCircuit (numericalPhaseBudget n t) (localQFT n))
        = (localQFT n).length ∧
      QueryCount (numericalDyadicCircuit (numericalPhaseBudget n t) (localQFT n)) = 0 ∧
      localProgramMatrix (localQFT n) =
        relabelGate (bitVecEquiv n).symm (QFTMatrix (2 ^ n)) ∧
      GateCount (localProgramCircuit (localQFT n)) = n + n * (n - 1) / 2 + n / 2 ∧
      QueryCount (localProgramCircuit (localQFT n)) = 0 := by
  have hborn := (numerical_qft_forward_inverse_born_budget n t ψ S hψ).1
  have hrun := numericalDyadicProgram_run n (numericalPhaseBudget n t) (localQFT n) ψ
  have hexact := Qatlib.Concepts.QftPreparation.LocalQft.aqLocalQFT_actual_matrix_and_cost n
  refine ⟨?_, hrun.2.2.2.2, hrun.2.2.2.1, hexact.1, hexact.2.1, hexact.2.2⟩
  simpa using hborn

theorem numericalPhaseBudget_eq (n t : ℕ) : numericalPhaseBudget n t = t + 2 * n + 6 := by
  unfold numericalPhaseBudget
  omega

end Qatlib.Papers.HiddenShift02.MainResults.FieldFourier
