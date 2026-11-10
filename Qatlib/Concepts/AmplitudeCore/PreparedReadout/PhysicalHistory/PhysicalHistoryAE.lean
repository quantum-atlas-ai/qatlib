/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.PaidHistoryWord
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.PhysicalHistoryAE
open Matrix
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.QspSimulation.JacobiAnger
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory

open Qatlib.Concepts.OperatorAccess.EncodedAccess
open Qatlib.Concepts.InstrumentCore.PovmBridge
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement

open MeasureTheory
open scoped Classical BigOperators Interval Matrix.Norms.L2Operator

variable {I E : Type} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]
open PaidHistoryPreparation
set_option warningAsError false

noncomputable local instance executionDecidableEq (q a : ℕ) :
    DecidableEq (BinaryClockSingleCU.New q (Reg a × I)) :=
  BinaryClockSingleCU.newDecidableEq q (Reg a × I)

def preparation (α T eps : ℚ) (a m : ℕ) : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step
    (Whole (ProjectorPhysicalBudget.clockBits α T eps) a m I E)) :=
  PaidHistoryWord.instructions (ProjectorPhysicalBudget.clockBits α T eps) a m α T
    (ProjectorPhysicalBudget.precisionBits α T eps)

def instructions (α T eps Jbar : ℚ) (a m : ℕ) (s : E × I) :=
  Qatlib.Concepts.AmplitudeCore.PreparedReadout.RationalMultiSourceAE.instructions T (ProjectorPhysicalBudget.massCap Jbar eps) eps
    (preparation (I := I) (E := E) α T eps a m)
    (seed (ProjectorPhysicalBudget.clockBits α T eps) a m s)
    (PaidHistoryWord.event (ProjectorPhysicalBudget.clockBits α T eps) a m)

def decode (T eps Jbar : ℚ)
    (z : Fin (Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.grid
      T (ProjectorPhysicalBudget.massCap Jbar eps) eps)) : ℚ :=
  Qatlib.Concepts.AmplitudeCore.PreparedReadout.RationalMultiSourceAE.decode T (ProjectorPhysicalBudget.massCap Jbar eps) eps z

def output (α T eps Jbar : ℚ) (a m : ℕ)
    (UH : Matrix (Reg a × I) (Reg a × I) ℂ) (P : Matrix (E × I) (E × I) ℂ)
    (UPi : Matrix (Reg m × I) (Reg m × I) ℂ) (s : E × I) :=
  Qatlib.Concepts.AmplitudeCore.PreparedReadout.RationalMultiSourceAE.output T (ProjectorPhysicalBudget.massCap Jbar eps) eps
    (PaidHistoryWord.sources (ProjectorPhysicalBudget.clockBits α T eps) a m UH P UPi)
    (preparation α T eps a m)
    (seed (ProjectorPhysicalBudget.clockBits α T eps) a m s)
    (PaidHistoryWord.event (ProjectorPhysicalBudget.clockBits α T eps) a m)

theorem success (α T eps Jbar : ℚ) (hα : 0 < α) (hT : 0 < T) (heps : 0 < eps)
    (a m : ℕ) (H Pi : Matrix I I ℂ) (hH : H.IsHermitian)
    (UH : Matrix (Reg a × I) (Reg a × I) ℂ)
    (hHenc : ProjectedUnitaryEncoding (BinaryClockPhysicalTime.normalized α H) UH
      (encodingFiber (I := I) (ZeroStr a)) (encodingFiber (I := I) (ZeroStr a)))
    (P : Matrix (E × I) (E × I) ℂ) (hP : P ∈ Matrix.unitaryGroup (E × I) ℂ)
    (UPi : Matrix (Reg m × I) (Reg m × I) ℂ)
    (hPi : ProjectedUnitaryEncoding Pi UPi (encodingFiber (I := I) (ZeroStr m))
      (encodingFiber (I := I) (ZeroStr m))) (hstar : Piᴴ = Pi) (hsq : Pi * Pi = Pi)
    (s : E × I)
    (hJbar : (∫ t in (0:ℝ)..(T:ℝ), ProjectorHistoryBorn.physicalReadout H Pi
      (purifiedDensity (P *ᵥ Qatlib.Foundations.PureStateMath.Ket s)) t) ≤ (Jbar : ℝ)) :
    MeasureProb (output α T eps Jbar a m UH P UPi s)
      (Finset.univ.filter (fun z => |(decode T eps Jbar z.1 : ℝ) -
        (∫ t in (0:ℝ)..(T:ℝ), ProjectorHistoryBorn.physicalReadout H Pi
          (purifiedDensity (P *ᵥ Qatlib.Foundations.PureStateMath.Ket s)) t)| ≤
            7*(eps:ℝ)/8)) ≥ 8/Real.pi^2 := by
  let q := ProjectorPhysicalBudget.clockBits α T eps
  let k := ProjectorPhysicalBudget.precisionBits α T eps
  let ψ := P *ᵥ Qatlib.Foundations.PureStateMath.Ket s
  let O := PaidHistoryWord.sources q a m UH P UPi
  let A := preparation (I := I) (E := E) α T eps a m
  let b := seed q a m s
  let S := PaidHistoryWord.event (I := I) (E := E) q a m
  have hψ := prepared_normalized P hP s
  have hp : Qatlib.Concepts.AmplitudeCore.PreparedReadout.RationalMultiSourceAE.amplitude O A b S =
      BinaryClockProjectorAccuracy.actualProbability α T eps a m UH UPi ψ :=
    PaidHistoryWord.actual_probability q a m α T k UH P UPi s
  have hb := BinaryClockProjectorAccuracy.actual_integral_bias α T eps hα hT heps
    a m H Pi hH UH hHenc UPi hPi hstar hsq ψ hψ
  have hm := BinaryClockProjectorAccuracy.actual_mass_le_cap α T eps Jbar hα hT heps
    a m H Pi hH UH hHenc UPi hPi hstar hsq ψ hψ hJbar
  rw [← hp] at hb hm
  exact Qatlib.Concepts.AmplitudeCore.PreparedReadout.RationalMultiSourceAE.success_to_center T (ProjectorPhysicalBudget.massCap Jbar eps) eps hT heps O A b S
    (PaidHistoryWord.sources_unitary q a m UH hHenc.unitary P hP UPi hPi.unitary)
    (PaidHistoryWord.instructions_wellFormed q a m α T k H hH UH hHenc)
    hm _ (by simpa only [abs_sub_comm] using! hb)

theorem resources (α T eps Jbar : ℚ) (a m : ℕ) (s : E × I)
    (H : Matrix I I ℂ) (hH : H.IsHermitian)
    (UH : Matrix (Reg a × I) (Reg a × I) ℂ)
    (henc : ProjectedUnitaryEncoding (BinaryClockPhysicalTime.normalized α H) UH
      (encodingFiber (I := I) (ZeroStr a)) (encodingFiber (I := I) (ZeroStr a))) :
    let q := ProjectorPhysicalBudget.clockBits α T eps
    let k := ProjectorPhysicalBudget.precisionBits α T eps
    let M :=
        Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.grid T
        (ProjectorPhysicalBudget.massCap Jbar eps) eps
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed (instructions α T eps Jbar a m s) ∧
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount .preparation (instructions α T eps Jbar a m s) = 2*M-1 ∧
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount .projector (instructions α T eps Jbar a m s) = 2*M-1 ∧
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount .hamiltonian (instructions α T eps Jbar a m s) =
      (2*M-1) * BinaryClockSignalCost.queryLedger q (α*T) k ∧
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.gateCount (instructions α T eps Jbar a m s) =
      (2*M-1) * (adjointGateCount
        (BinaryClockSignalWord.instructions q (encodingFiber (I := I) (ZeroStr a)) (α*T) k) +
          2 * BinaryClockSignalCost.queryLedger q (α*T) k + 7) + 4*(M-1)+2 := by
  let q := ProjectorPhysicalBudget.clockBits α T eps
  let k := ProjectorPhysicalBudget.precisionBits α T eps
  let A := preparation (I := I) (E := E) α T eps a m
  let b := seed q a m s
  let ev := PaidHistoryWord.event (I := I) (E := E) q a m
  have hw := PaidHistoryWord.instructions_wellFormed (E := E) q a m α T k H hH UH henc
  have hr :=
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.RationalMultiSourceAE.resources T
      (ProjectorPhysicalBudget.massCap Jbar eps) eps A b ev hw
  have hi : instructions α T eps Jbar a m s =
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.RationalMultiSourceAE.instructions
        T (ProjectorPhysicalBudget.massCap Jbar eps) eps A b ev := rfl
  rw [← hi] at hr
  have hc := PaidHistoryWord.instructions_counts (I := I) (E := E) q a m α T k
  have hA : A = PaidHistoryWord.instructions (I := I) (E := E) q a m α T k := rfl
  rw [← hA] at hc
  have hp := BinaryClockPhysicalTime.resources q α T k H UH
    (encodingFiber (I := I) (ZeroStr a)) hH henc
  refine ⟨hr.1, ?_, ?_, ?_, ?_⟩
  · rw [hr.2.1 .preparation, hc.2.1, mul_one]
  · rw [hr.2.1 .projector, hc.2.2.1, mul_one]
  · rw [hr.2.1 .hamiltonian, hc.1, hp.2.1]
  · rw [hr.2.2, hc.2.2.2, hp.2.2]

end Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.PhysicalHistoryAE
