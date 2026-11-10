/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.DynamicKernelFamily
import Qatlib.Papers.Cbmd26.Algorithms.CountedAmplificationBridge
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
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
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
noncomputable section
namespace CBMD
open Matrix
open scoped Matrix.Norms.L2Operator ENNReal

def dynamicZeroTimeWord (I : Type) : List (PreparedStep I) := [.prepareForward]

section Matrices
variable {I : Type} [Fintype I] [DecidableEq I]

theorem dynamic_zero_time_identity {H L : ℝ → Matrix I I ℂ}
    (P : _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.FinitePiecewiseContinuousOn (fun u => (H u, L u)) 0 0) (z : ℂ) :
    P.evolution z 0 = 1 := P.evolution_initial z

theorem dynamicZeroTimeWord_evaluate_and_counts (O B : Matrix I I ℂ) :
    PreparedCircuitValid (dynamicZeroTimeWord I) ∧
    evaluatePrepared O B (dynamicZeroTimeWord I) = B ∧
    preparedDataQueries (dynamicZeroTimeWord I) = 0 ∧
    preparedInputQueries (dynamicZeroTimeWord I) = 1 ∧
    preparedFixedGates (dynamicZeroTimeWord I) = 0 := by
  refine ⟨?_, ?_, rfl, rfl, rfl⟩
  · intro c hc
    have he : c = .prepareForward := List.mem_singleton.mp hc
    subst c
    trivial
  · simp [dynamicZeroTimeWord, evaluatePrepared, preparedInstruction]

theorem fullSystemHerald_exact (ψ : QState I) (hψ : Normalized ψ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
      (projectiveHeraldLaw (Projector (Finset.univ : Finset I))
        (projector_isOrthogonalProjector _) ψ hψ) (fun b => b = true) = 1 ∧
    ProjectiveConditionalState (Projector (Finset.univ : Finset I)) true ψ = some ψ := by
  have hc : Collapse ψ Finset.univ = ψ := by
    funext i
    simp [collapse_apply]
  have hp : MeasureProb ψ Finset.univ = 1 := measureProb_univ hψ
  constructor
  · rw [projectiveHeraldLaw_success]
    simp only [ProjectiveBranchMass, projectiveBranch_projector, hc, hp, ENNReal.ofReal_one]
  · change ConditionalState (Collapse ψ Finset.univ) = some ψ
    rw [hc]
    have hn := (normalized_iff_stateVector_norm ψ).mp hψ
    simp only [ConditionalState, hp, zero_lt_one, if_true, postMeasure_univ_eq_smul, hn]
    simp

theorem dynamic_zero_time_program {H L : ℝ → Matrix I I ℂ}
    (P : _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.FinitePiecewiseContinuousOn (fun u => (H u, L u)) 0 0)
    (O B : Matrix I I ℂ) (hunitary : B ∈ Matrix.unitaryGroup I ℂ)
    (i₀ : I) (ψ : QState I) (hB : ApplyGate B (Ket i₀) = ψ) :
    PreparedCircuitValid (dynamicZeroTimeWord I) ∧
    preparedDataQueries (dynamicZeroTimeWord I) = 0 ∧
    preparedInputQueries (dynamicZeroTimeWord I) = 1 ∧
    preparedFixedGates (dynamicZeroTimeWord I) = 0 ∧
    evaluatePrepared O B (dynamicZeroTimeWord I) ∈ Matrix.unitaryGroup I ℂ ∧
    ApplyGate (evaluatePrepared O B (dynamicZeroTimeWord I)) (Ket i₀) = ψ ∧
    IsNormalizedApplication (P.evolution (-Complex.I) 0) ψ
      (ApplyGate (evaluatePrepared O B (dynamicZeroTimeWord I)) (Ket i₀)) 0 ∧
    ∃ hφ : Normalized (ApplyGate (evaluatePrepared O B (dynamicZeroTimeWord I)) (Ket i₀)),
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
        (projectiveHeraldLaw (Projector (Finset.univ : Finset I))
          (projector_isOrthogonalProjector _)
          (ApplyGate (evaluatePrepared O B (dynamicZeroTimeWord I)) (Ket i₀)) hφ)
        (fun b => b = true) = 1 ∧
      ProjectiveConditionalState (Projector (Finset.univ : Finset I)) true
        (ApplyGate (evaluatePrepared O B (dynamicZeroTimeWord I)) (Ket i₀)) = some ψ := by
  obtain ⟨hv, he, hq, hb, hg⟩ := dynamicZeroTimeWord_evaluate_and_counts O B
  have hψ : Normalized ψ := by
    rw [← hB]
    exact normalized_applyGate hunitary (normalized_ket i₀)
  have hout : ApplyGate (evaluatePrepared O B (dynamicZeroTimeWord I)) (Ket i₀) = ψ := by
    rw [he, hB]
  refine ⟨hv, hq, hb, hg, he.symm ▸ hunitary, hout, ?_, ?_⟩
  · rw [dynamic_zero_time_identity, hout]
    have hn := (normalized_iff_stateVector_norm ψ).mp hψ
    refine ⟨?_, hψ, ?_⟩
    · rw [Matrix.one_mulVec]
      intro hz
      rw [hz] at hn
      simp [stateVector] at hn
    · simp only [Matrix.one_mulVec, NormedSpace.normalize_eq_self_of_norm_eq_one hn,
        sub_self, norm_zero, le_refl]
  · have hφ : Normalized (ApplyGate (evaluatePrepared O B (dynamicZeroTimeWord I)) (Ket i₀)) :=
      hout.symm ▸ hψ
    refine ⟨hφ, (fullSystemHerald_exact _ hφ).1, ?_⟩
    rw [(fullSystemHerald_exact _ hφ).2, hout]

end Matrices
end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
