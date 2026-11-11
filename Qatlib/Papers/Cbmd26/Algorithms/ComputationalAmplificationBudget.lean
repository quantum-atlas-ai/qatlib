/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.ComputationalAmplificationBridge

/-!
# Explicit budgets for computational amplification

The predicate `BudgetedComputationalAmplificationResult` repackages computational workspace
amplification using user-supplied input and data query budgets. Enlarging the established
expected bounds also supplies per-choice bounds four times the respective budgets. These results
support the contour-based algorithms of [WangEtAl2026].

## Main statements

* `BudgetedComputationalAmplificationResult`: records amplification with budgets `R` and `Q`.
* `computationalAmplificationResult_budget`: transfers an existing amplification result to
  larger budgets.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

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
noncomputable section
namespace CBMD
open Matrix
open scoped Matrix.Norms.L2Operator ENNReal
variable {W Aux I : Type} [Fintype W] [DecidableEq W] [Fintype Aux] [DecidableEq Aux]
  [Fintype I] [DecidableEq I]

/-- Records computational-event amplification with expected input and data query budgets `R` and
`Q`, per-choice budgets `4 * R` and `4 * Q`, and the heralding and normalized output
guarantees. -/
def BudgetedComputationalAmplificationResult (e : W ≃ Aux × I) (a₀ : Aux)
    (O : Matrix W W ℂ) (cs : List (AdjointStep W)) (B : Matrix I I ℂ)
    (i₀ : I) (ψ : QState I) (target : Matrix I I ℂ) (ε η R Q : ℝ) : Prop :=
  let m := staticAmplificationWindow η
  ∃ hm : NeZero m,
  letI := hm
  let Bin := computationalWorkspaceInput e B
  let zero := e.symm (a₀,i₀)
  let S := computationalWorkspaceEvent e a₀
  let A := evaluate O cs * Bin
  ∃ (_hcs : WellFormedAdjointCircuit cs) (hA : A ∈ Matrix.unitaryGroup W ℂ),
    ENNReal.ofReal (1/8 : ℝ) ≤
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (randomizedAAHerald A hA zero S m) (fun x => x.2 = true) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (randomizedAAHerald A hA zero S m)
      (fun x => (preparedInputQueries
        (countedAAWord (preparedTrial cs) zero S (aaRounds x.1)) : ℝ≥0∞)) ≤
      ENNReal.ofReal R ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (randomizedAAHerald A hA zero S m)
      (fun x => (preparedDataQueries
        (countedAAWord (preparedTrial cs) zero S (aaRounds x.1)) : ℝ≥0∞)) ≤
      ENNReal.ofReal Q ∧
    (∀ choice : Bool × Fin m,
      (preparedInputQueries (countedAAWord (preparedTrial cs) zero S (aaRounds choice)) : ℝ) ≤
        4 * R ∧
      (preparedDataQueries (countedAAWord (preparedTrial cs) zero S (aaRounds choice)) : ℝ) ≤
        4 * Q) ∧
    (∀ k, PreparedCircuitValid (countedAAWord (preparedTrial cs) zero S k) ∧
      ApplyGate (evaluatePrepared O Bin (countedAAWord (preparedTrial cs) zero S k)) (Ket zero) =
        Run (preparedMark S) (preparedAACircuit A zero k) (Ket zero)) ∧
    (∀ choice : Bool × Fin m,
      (choice, true) ∈ (randomizedAAHerald A hA zero S m).support →
      ∃ (y : QState I) (z : ℂ),
        ConditionalState ((computationalWorkspaceFrame e a₀)ᴴ *ᵥ
          Run (preparedMark S) (preparedAACircuit A zero (aaRounds choice)) (Ket zero)) = some y ∧
        ‖z‖ = 1 ∧ Normalized y ∧ IsNormalizedApplication target ψ ((star z) • y) ε)

omit [Fintype Aux] in

/-- An existing computational amplification result satisfies the budgeted result whenever `R`
and `Q` dominate its established query bounds. -/
theorem computationalAmplificationResult_budget (e : W ≃ Aux × I) (a₀ : Aux)
    (O : Matrix W W ℂ) (cs : List (AdjointStep W)) (B : Matrix I I ℂ)
    (i₀ : I) (ψ : QState I) (target : Matrix I I ℂ) (ε η R Q : ℝ)
    (h : ComputationalAmplificationResult e a₀ O cs B i₀ ψ target ε η)
    (hR : (4 * staticMassBudget + 1) / η ≤ R)
    (hQ : ((4 * staticMassBudget + 1) / η) * (adjointQueryCount cs : ℝ) ≤ Q) :
    BudgetedComputationalAmplificationResult e a₀ O cs B i₀ ψ target ε η R Q := by
  obtain ⟨hm, hcs, hA, hs, hi, hd, hp, hr, ho⟩ := h
  letI := hm
  refine ⟨hm, hcs, hA, hs, hi.trans (ENNReal.ofReal_le_ofReal hR),
    hd.trans (ENNReal.ofReal_le_ofReal hQ), ?_, hr, ho⟩
  intro choice
  obtain ⟨hip, hdp⟩ := hp choice
  constructor
  · calc
      _ ≤ 4 * (4 * staticMassBudget + 1) / η := hip
      _ = 4 * ((4 * staticMassBudget + 1) / η) := by ring
      _ ≤ 4 * R := mul_le_mul_of_nonneg_left hR (by norm_num)
  · calc
      _ ≤ 4 * ((4 * staticMassBudget + 1) / η) * (adjointQueryCount cs : ℝ) := hdp
      _ = 4 * (((4 * staticMassBudget + 1) / η) * (adjointQueryCount cs : ℝ)) := by ring
      _ ≤ 4 * Q := mul_le_mul_of_nonneg_left hQ (by norm_num)

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
