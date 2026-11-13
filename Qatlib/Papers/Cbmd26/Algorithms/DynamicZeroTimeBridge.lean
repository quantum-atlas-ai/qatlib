/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.DynamicKernelFamily
import Qatlib.Papers.Cbmd26.Algorithms.CountedAmplificationBridge

/-!
# Exact state preparation at zero evolution time

`dynamicZeroTimeWord` consists of one input-preparation step. Since the piecewise evolution at
time zero is the identity, this word produces the initial state exactly, and projection onto the
full system succeeds with probability one. The module covers the zero-time case of the dynamic
construction in [WangEtAl2026].

## Main statements

* `dynamicZeroTimeWord_evaluate_and_counts`: evaluates the word and records its zero data
  queries, one input query, and zero fixed gates.
* `dynamic_zero_time_program`: packages exact normalized evolution and the certain heralding
  event.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

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

/-- The zero-time circuit word consisting of a single forward input-preparation step. -/
def dynamicZeroTimeWord (I : Type) : List (PreparedStep I) := [.prepareForward]

section Matrices
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The piecewise evolution on the interval from zero to zero is the identity for every complex
parameter. -/
theorem dynamic_zero_time_identity {H L : ℝ → Matrix I I ℂ}
    (P : _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.FinitePiecewiseContinuousOn (fun u => (H u, L u)) 0 0) (z : ℂ) :
    P.evolution z 0 = 1 := P.evolution_initial z

/-- The zero-time word is valid and evaluates to the input-preparation matrix `B`, using zero
data queries, one input query, and zero fixed gates. -/
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

/-- Projection onto the full system succeeds with probability one on a normalized state and
leaves its conditional state equal to the original state. -/
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

/-- A unitary input-preparation matrix gives an exact normalized application of the zero-time
evolution with zero data queries, one input query, and zero fixed gates. The full-system
herald succeeds with probability one and returns the prepared state. -/
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
