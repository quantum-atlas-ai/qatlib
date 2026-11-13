/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.NativeNumerics.NumericalQFT
import Qatlib.Concepts.QftPreparation.LocalQft

/-!
# Exact and numerical Fourier circuits

This module packages the matrix semantics and resource counts of the local quantum Fourier
transform. The theorem `source_lemma2` also bounds event-probability error by 2^(−t) for its
numerical dyadic implementation, using the explicit precision `numericalPhaseBudget`.

The development follows [VanDamHallgrenIp2006].

## Main statements

* `source_lemma2_exact`: The local Fourier program implements the relabeled Fourier matrix on
  2^n basis states, with n + n(n − 1)/2 + n/2 gates and no oracle queries.
* `source_lemma2`: For a normalized input, the numerical dyadic circuit approximates every
  measurement-event probability of the exact Fourier gate within 2^(−t). It also records the
  numerical and exact circuit counts and exact matrix semantics.
* `numericalPhaseBudget_eq`: The precision budget for the numerical Fourier circuit is t + 2n +
  6.

## References

* [van Dam et al., 2006][VanDamHallgrenIp2006]
-/

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

/-- The local Fourier program implements the relabeled Fourier matrix on 2^n basis states, with
n + n(n − 1)/2 + n/2 gates and no oracle queries ([Lemma 2][VanDamHallgrenIp2006]). -/
theorem source_lemma2_exact (n : ℕ) :
    localProgramMatrix (localQFT n) =
        relabelGate (bitVecEquiv n).symm (QFTMatrix (2 ^ n)) ∧
      GateCount (localProgramCircuit (localQFT n)) = n + n * (n - 1) / 2 + n / 2 ∧
      QueryCount (localProgramCircuit (localQFT n)) = 0 :=
  Qatlib.Concepts.QftPreparation.LocalQft.aqLocalQFT_actual_matrix_and_cost n

/-- For a normalized input, the numerical dyadic circuit approximates every measurement-event
probability of the exact Fourier gate within 2^(−t). It also records the numerical and exact
circuit counts and exact matrix semantics ([Lemma 2][VanDamHallgrenIp2006]). -/
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

/-- The precision budget for the numerical Fourier circuit is t + 2n + 6 ([Lemma
2][VanDamHallgrenIp2006]). -/
theorem numericalPhaseBudget_eq (n t : ℕ) : numericalPhaseBudget n t = t + 2 * n + 6 := by
  unfold numericalPhaseBudget
  omega

end Qatlib.Papers.HiddenShift02.MainResults.FieldFourier
