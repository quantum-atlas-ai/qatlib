/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.UniformPropagatorApproximation
import Qatlib.Papers.Cbmd26.Algorithms.ThreeOracleAmplification
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SignalPrimitive.HermitianQSVT
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
noncomputable section
namespace CBMD
open Matrix
open scoped Matrix.Norms.L2Operator

@[simp] theorem secondOrderPropagator_zero {I : Type} [Fintype I] [DecidableEq I]
    (kind : SecondOrderFamily) (A : Matrix I I ℂ) : secondOrderPropagator kind A 0 = 1 := by
  cases kind <;> simp [secondOrderPropagator]

theorem secondOrder_zero_time_program {I : Type} [Fintype I] [DecidableEq I]
    (kind : SecondOrderFamily) (A O1 O2 B : Matrix I I ℂ)
    (hunitary : B ∈ Matrix.unitaryGroup I ℂ) (i₀ : I)
    (ψ : QState I) (hψ : Normalized ψ) (hB : ApplyGate B (Ket i₀) = ψ) :
    let cs : List (ThreeOracleStep I) := [.stateForward]
    ThreeCircuitValid cs ∧
    threeFirstQueries cs = 0 ∧ threeSecondQueries cs = 0 ∧ threeStateQueries cs = 1 ∧
    evaluateThree O1 O2 B cs ∈ Matrix.unitaryGroup I ℂ ∧
    ApplyGate (evaluateThree O1 O2 B cs) (Ket i₀) = ψ ∧
    IsNormalizedApplication (secondOrderPropagator kind A 0) ψ
      (ApplyGate (evaluateThree O1 O2 B cs) (Ket i₀)) 0 := by
  (try dsimp only)
  have he : ApplyGate (evaluateThree O1 O2 B [.stateForward]) (Ket i₀) = ψ := by
    simpa [evaluateThree, threeInstruction] using! hB
  have hu : evaluateThree O1 O2 B [.stateForward] ∈ Matrix.unitaryGroup I ℂ := by
    simpa [evaluateThree, threeInstruction] using! hunitary
  refine ⟨?_, rfl, rfl, rfl, hu, he, ?_⟩
  · intro c hc
    simp only [List.mem_singleton] at hc
    subst c
    trivial
  rw [secondOrderPropagator_zero, he]
  have hn := (normalized_iff_stateVector_norm ψ).mp hψ
  refine ⟨?_, hψ, ?_⟩
  · rw [Matrix.one_mulVec]
    intro hz
    rw [hz] at hn
    simp [stateVector] at hn
  · simp only [Matrix.one_mulVec, NormedSpace.normalize_eq_self_of_norm_eq_one hn,
      sub_self, norm_zero, le_refl]

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
