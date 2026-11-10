/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.OriginalAStaticConsumer
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
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace CBMD
open Matrix Polynomial
open scoped BigOperators Matrix.Norms.L2Operator ENNReal

variable {J W I : Type} [Fintype J] [DecidableEq J] [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I]

local instance cbmdOriginalAStaticAmplificationInstance1 : DecidableEq (OriginalStaticLabels J) :=
  inferInstanceAs (DecidableEq (J × (Fin 4 × (Bool × (Bool × Bool)))))

abbrev OriginalStaticSpace (J W : Type) := Bool × (OriginalStaticLabels J × W)

theorem originalA_static_amplified_target
    (L H : Matrix I I ℂ) (hL : L.IsHermitian) (hH : H.IsHermitian)
    (U : Matrix W W ℂ) (R : Matrix W I ℂ) (α Λ t ε δ : ℝ) (s : J → ℝ)
    (henc : BlockEncoding (L + Complex.I • H) U R R α 0)
    (hΛ : 0 < Λ) (hε : 0 < ε) (hδ : 0 ≤ δ)
    (hbound : ∀ j, α * Real.sqrt (1 + (s j)^2) ≤ Λ)
    (c : J → ℂ) (j₀ : J) (hc : 0 < coefficientMass c)
    (target : Matrix I I ℂ)
    (htail : ‖target - ∑ j, c j •
      NormedSpace.exp ((-Complex.I * (t : ℂ)) • (H + (s j : ℂ) • L))‖ ≤ δ)
    (B : Matrix (OriginalStaticSpace J W) (OriginalStaticSpace J W) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (OriginalStaticSpace J W) ℂ)
    (zero : OriginalStaticSpace J W) (S : Finset (OriginalStaticSpace J W))
    (ψ : QState I) (hψ : Normalized ψ)
    (hprepare : ApplyGate B (Ket zero) = originalStaticFrame R j₀ *ᵥ ψ)
    (hproject : rangeProjector (originalStaticFrame R j₀) = Projector S)
    (η : ℝ) (hη : 0 < η) (htarget : η ≤ ‖stateVector (target *ᵥ ψ)‖)
    (herror : ε * coefficientMass c + δ ≤ η / 2)
    (m : ℕ) [NeZero m] (hwindow : 8 * coefficientMass c / η ≤ (m : ℝ)) :
    ∃ (P : Polynomial ℂ) (base : Fin 4 → ℂ) (zs : Fin 4 → List ℂ),
      let d := ComplexPolynomialSplit.branchDegrees (normalizedApproximation P (ε/2))
      let cs := originalStaticOuterWord R α Λ s c j₀ d base zs
      let O := controlOracle (parallelOracle (J := OriginalStaticLabels J) U)
      let A := evaluate O cs * B
      ∃ (_hcs : WellFormedAdjointCircuit cs) (hA : A ∈ Matrix.unitaryGroup (OriginalStaticSpace J W) ℂ),
        adjointQueryCount cs ≤
          8 * (2 * dyadicOrder ((ε/2) / (2 * Real.exp (2 * |t * Λ|))) + 1) ∧
        ENNReal.ofReal (1/8 : ℝ) ≤
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (randomizedAAHerald A hA zero S m) (fun x => x.2 = true) ∧
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (randomizedAAHerald A hA zero S m)
          (fun x => (preparedInputQueries
            (countedAAWord (preparedTrial cs) zero S (aaRounds x.1)) : ℝ≥0∞)) =
          ENNReal.ofReal (((m : ℝ) + 1) / 2) ∧
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (randomizedAAHerald A hA zero S m)
          (fun x => (preparedDataQueries
            (countedAAWord (preparedTrial cs) zero S (aaRounds x.1)) : ℝ≥0∞)) =
          ENNReal.ofReal ((((m : ℝ) + 1) / 2) * (2 * (∑ k, (zs k).length) : ℕ)) ∧
        (∀ k, PreparedCircuitValid (countedAAWord (preparedTrial cs) zero S k) ∧
          ApplyGate (evaluatePrepared O B (countedAAWord (preparedTrial cs) zero S k)) (Ket zero) =
            Run (preparedMark S) (preparedAACircuit A zero k) (Ket zero)) ∧
        (∀ choice : Bool × Fin m,
          (choice, true) ∈ (randomizedAAHerald A hA zero S m).support →
          ∃ (y : QState I) (z : ℂ),
            ConditionalState ((originalStaticFrame R j₀)ᴴ *ᵥ
              Run (preparedMark S) (preparedAACircuit A zero (aaRounds choice)) (Ket zero)) = some y ∧
            ‖z‖ = 1 ∧ Normalized y ∧
            IsNormalizedApplication target ψ ((star z) • y)
              (2 * (ε * coefficientMass c + δ) / ‖stateVector (target *ᵥ ψ)‖)) := by
  obtain ⟨P, base, zs, _, _, hcs, he, hq⟩ := originalA_static_exponential_outer
    L H hL hH U R α Λ t ε s henc hΛ hε hbound c j₀ hc
  let d := ComplexPolynomialSplit.branchDegrees (normalizedApproximation P (ε/2))
  let cs := originalStaticOuterWord R α Λ s c j₀ d base zs
  let O := controlOracle (parallelOracle (J := OriginalStaticLabels J) U)
  have hO : O ∈ Matrix.unitaryGroup (OriginalStaticSpace J W) ℂ :=
    controlOracle_unitary (parallelOracle_unitary henc.unitary)
  have ht : BlockEncoding target (evaluate O cs) (originalStaticFrame R j₀)
      (originalStaticFrame R j₀) (4 * coefficientMass c) (ε * coefficientMass c + δ) :=
    he.perturb hδ htail
  have hA : evaluate O cs * B ∈ Matrix.unitaryGroup (OriginalStaticSpace J W) ℂ :=
    (Matrix.unitaryGroup _ ℂ).mul_mem ht.unitary hB
  have haa := counted_blockEncoding_randomized_amplification target O B cs hO hB hcs
    (originalStaticFrame R j₀) (originalStaticFrame R j₀)
    (4 * coefficientMass c) (ε * coefficientMass c + δ) η ht zero S ψ hψ
    hprepare hproject hη htarget herror m (by convert! hwindow using 1; ring)
  simp only [evaluate_preparedTrial] at haa
  refine ⟨P, base, zs, hcs, hA, hq, haa.1, haa.2.1, ?_, haa.2.2.2.1, ?_⟩
  · have hcount := (originalStaticOuterWord_cost R α Λ s c j₀ d base zs).1
    change adjointQueryCount cs = _ at hcount
    simpa only [hcount] using! haa.2.2.1
  · intro choice hsupport
    apply blockEncoding_randomized_supported_output target (evaluate O cs) B
      (originalStaticFrame R j₀) (originalStaticFrame R j₀)
      (4 * coefficientMass c) (ε * coefficientMass c + δ) ht hB zero S ψ hψ
      hprepare hproject _ m choice hsupport
    linarith

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
