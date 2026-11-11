/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.ThreeOracleAmplification

/-!
# Pathwise costs from randomized amplification means

The finite randomized amplification window bounds the cost of each random choice in terms of its
mean repetition count. This module converts separate expected matrix and state budgets into
pathwise bounds for the three-oracle framework of [WangEtAl2026].

## Main statements

* `threeAAWord_worst_case_from_mean`: every choice uses at most four times each supplied
  mean-cost budget.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false

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

variable {H : Type} [Fintype H] [DecidableEq H]

/-- Bounds on the mean repetition costs imply that every random choice uses at most `4 *
matrixBudget` queries to each matrix oracle and `4 * stateBudget` state queries. -/
theorem threeAAWord_worst_case_from_mean (body : List (PreparedStep H))
    (zero : H) (S : Finset H) (m : ℕ) [NeZero m] (matrixBudget stateBudget : ℝ)
    (h1 : (((m : ℝ) + 1) / 2) * preparedDataQueries body ≤ matrixBudget)
    (h2 : (((m : ℝ) + 1) / 2) * preparedInputQueries body ≤ matrixBudget)
    (h3 : ((m : ℝ) + 1) / 2 ≤ stateBudget) (choice : Bool × Fin m) :
    (threeFirstQueries (threeAAWord body zero S (aaRounds choice)) : ℝ) ≤ 4 * matrixBudget ∧
    (threeSecondQueries (threeAAWord body zero S (aaRounds choice)) : ℝ) ≤ 4 * matrixBudget ∧
    (threeStateQueries (threeAAWord body zero S (aaRounds choice)) : ℝ) ≤ 4 * stateBudget := by
  obtain ⟨hq1,hq2,hqs⟩ := threeAAWord_path_budget body zero S m choice
  have hnat : 2 * m - 1 ≤ 2 * m + 2 := by omega
  constructor
  · calc
      _ ≤ (((2 * m + 2) * preparedDataQueries body : ℕ) : ℝ) :=
        Nat.cast_le.mpr (hq1.trans (Nat.mul_le_mul_right _ hnat))
      _ = 4 * ((((m : ℝ) + 1) / 2) * preparedDataQueries body) := by push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by norm_num)
  constructor
  · calc
      _ ≤ (((2 * m + 2) * preparedInputQueries body : ℕ) : ℝ) :=
        Nat.cast_le.mpr (hq2.trans (Nat.mul_le_mul_right _ hnat))
      _ = 4 * ((((m : ℝ) + 1) / 2) * preparedInputQueries body) := by push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by norm_num)
  · calc
      _ ≤ ((2 * m + 2 : ℕ) : ℝ) := Nat.cast_le.mpr (hqs.trans hnat)
      _ = 4 * (((m : ℝ) + 1) / 2) := by push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by norm_num)

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
