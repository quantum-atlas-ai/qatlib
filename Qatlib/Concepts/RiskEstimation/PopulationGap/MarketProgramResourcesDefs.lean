/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PopulationGap.AmplitudeReadoutDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.NativeRiskDefs
import Qatlib.Concepts.NativeNumerics.EmpiricalRisk.EmpiricalRiskConsumers
import Qatlib.Concepts.RiskEstimation.VaRQuantile.BisectFiniteRoutingSubgoalQuan
import Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
import Qatlib.Concepts.CircuitImpl.MultiControl.NoWorkTwoLevelSynthesis
import Qatlib.Concepts.RiskEstimation.PopulationGap.Implementation
import Qatlib.Concepts.RiskEstimation.PopulationGap.ImplementationDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.GatesDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.OrderShorDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.ContinuousMarketCDFDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.MarketQuantizationDefs

/-!
# Market grid scan resource accounting

This module records sample counts, table scans, comparisons, amplitude estimation records,
queries, and gates for a finite market threshold scan. `marketProgramResources` expresses each
cost in terms of the number of visited thresholds and median repetitions in the quantum risk
setting of [WoernerEgger2019].

The accounting identities are combined with a finite grid sampling bound by
`marketGrid_cost_accuracy`.

## Main statements

* `marketTableRead_eq_empiricalCDF`: a threshold count equals sample size times the empirical
  CDF.
* `marketProgram_quantum_charges`: forward, backward, query, and gate counts.
* `marketGrid_cost_accuracy`: resource identities and a uniform sampling error probability
  bound.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree

open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib
open Matrix
open scoped ENNReal Classical BigOperators
open Qatlib
open Qatlib.Concepts.RiskEstimation.CDFEstimation
open Qatlib.Concepts.RiskEstimation.CVaREstimation
open Qatlib
open Qatlib.Concepts.RiskEstimation.PopulationGap
open Qatlib.Concepts.RiskEstimation.VaRQuantile
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018
open Qatlib
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {I : Type} [Fintype I] [DecidableEq I]
variable {n N : ℕ}

namespace Qatlib.Concepts.RiskEstimation.PopulationGap

/-- Counts sample records whose loss is at most the threshold `t`. -/
noncomputable def marketTableRead {n N : ℕ} (ω : Fin N → Option (Fin n))
    (loss : Option (Fin n) → ℝ) (t : ℝ) : ℕ :=
  ∑ k, if loss (ω k) ≤ t then 1 else 0

/-- For positive sample size, the threshold count equals the empirical CDF multiplied by the
sample size. -/
theorem marketTableRead_eq_empiricalCDF {n N : ℕ} (ω : Fin N → Option (Fin n))
    (loss : Option (Fin n) → ℝ) (t : ℝ) (hN : 0 < N) :
    (marketTableRead ω loss t : ℝ) = marketEmpiricalCDF ω loss t * (N : ℝ) := by
  unfold marketTableRead marketEmpiricalCDF
  push_cast
  field_simp

/-- The number of grid thresholds scanned, defined as one plus the recorded crossing index
capped at `iT + 1`. -/
noncomputable def marketGridScan {n N : ℕ} (ω : Fin N → Option (Fin n))
    (loss : Option (Fin n) → ℝ) (Δ q : ℝ) (iT : ℕ) : ℕ :=
  min (marketGridRecordIndex ω loss Δ q iT + 1) (iT + 1)

/-- A grid scan visits at most `iT + 1` thresholds. -/
theorem marketGridScan_le {n N : ℕ} (ω : Fin N → Option (Fin n))
    (loss : Option (Fin n) → ℝ) (Δ q : ℝ) (iT : ℕ) :
    marketGridScan ω loss Δ q iT ≤ iT + 1 := by
  unfold marketGridScan
  exact min_le_right _ _

/-- If the recorded crossing index lies within the grid, the scan count is that index plus one. -/
theorem marketGridScan_eq_of_reached {n N : ℕ} (ω : Fin N → Option (Fin n))
    (loss : Option (Fin n) → ℝ) (Δ q : ℝ) (iT : ℕ)
    (h : marketGridRecordIndex ω loss Δ q iT ≤ iT) :
    marketGridScan ω loss Δ q iT = marketGridRecordIndex ω loss Δ q iT + 1 := by
  unfold marketGridScan
  exact Nat.min_eq_left (Nat.succ_le_succ h)

/-- Counts samples, table reads, record comparisons, amplitude estimation records, queries, and
gates. -/
structure MarketProgramResources where

  samples : ℕ

  tableReads : ℕ

  recordComparisons : ℕ

  aeRecords : ℕ

  queries : ℕ

  gates : ℕ

/-- The resource ledger for the recorded grid scan, using `2 * r + 1` amplitude estimation
records per visited threshold. -/
noncomputable def marketProgramResources {n N : ℕ} (M r : ℕ)
    (ω : Fin N → Option (Fin n)) (loss : Option (Fin n) → ℝ) (Δ q : ℝ)
    (iT : ℕ) : MarketProgramResources :=
  let reads := marketGridScan ω loss Δ q iT
  ⟨N, reads, reads * N, reads * (2*r+1), reads * (2*r+1) * (M-1),
    reads * (2*r+1) * (5*(M-1)+3)⟩

/-- The resource ledger's table read count equals `marketGridScan`. -/
theorem marketProgramResources_reads {n N : ℕ} (M r : ℕ)
    (ω : Fin N → Option (Fin n)) (loss : Option (Fin n) → ℝ) (Δ q : ℝ) (iT : ℕ) :
    (marketProgramResources M r ω loss Δ q iT).tableReads
      = marketGridScan ω loss Δ q iT := rfl

/-- The record comparison count equals the number of table reads times the sample count. -/
theorem marketProgramResources_comparisons {n N : ℕ} (M r : ℕ)
    (ω : Fin N → Option (Fin n)) (loss : Option (Fin n) → ℝ) (Δ q : ℝ) (iT : ℕ) :
    (marketProgramResources M r ω loss Δ q iT).recordComparisons
      = (marketProgramResources M r ω loss Δ q iT).tableReads
        * (marketProgramResources M r ω loss Δ q iT).samples := rfl

/-- The amplitude estimation record count is the table read count multiplied by `2 * r + 1`. -/
theorem marketProgramResources_ae {n N : ℕ} (M r : ℕ)
    (ω : Fin N → Option (Fin n)) (loss : Option (Fin n) → ℝ) (Δ q : ℝ) (iT : ℕ) :
    (marketProgramResources M r ω loss Δ q iT).aeRecords
      = (marketProgramResources M r ω loss Δ q iT).tableReads * (2*r+1) := rfl

/-- The query count is the amplitude estimation record count multiplied by `M - 1`. -/
theorem marketProgramResources_queries {n N : ℕ} (M r : ℕ)
    (ω : Fin N → Option (Fin n)) (loss : Option (Fin n) → ℝ) (Δ q : ℝ) (iT : ℕ) :
    (marketProgramResources M r ω loss Δ q iT).queries
      = (marketProgramResources M r ω loss Δ q iT).aeRecords * (M-1) := rfl

/-- The gate count is the amplitude estimation record count multiplied by `5 * (M - 1) + 3`. -/
theorem marketProgramResources_gates {n N : ℕ} (M r : ℕ)
    (ω : Fin N → Option (Fin n)) (loss : Option (Fin n) → ℝ) (Δ q : ℝ) (iT : ℕ) :
    (marketProgramResources M r ω loss Δ q iT).gates
      = (marketProgramResources M r ω loss Δ q iT).aeRecords * (5*(M-1)+3) := rfl

/-- For `M ≥ 2`, gives exact forward and backward access, query, and gate counts for all median
repetitions across the grid scan. -/
theorem marketProgram_quantum_charges {n N : ℕ}
    (B : Matrix (Option (Fin n)) (Option (Fin n)) ℂ) (j : Option (Fin n))
    (M r : ℕ) (hM : 2 ≤ M)
    (ω : Fin N → Option (Fin n)) (loss : Option (Fin n) → ℝ) (Δ q : ℝ) (iT : ℕ) :
    marketGridScan ω loss Δ q iT * (2*r+1)
        * aeForwardAccesses (aeAccessWord (I := Option (Fin n)) M)
      = marketGridScan ω loss Δ q iT * (2*r+1) * M ∧
    marketGridScan ω loss Δ q iT * (2*r+1)
        * aeBackwardAccesses (aeAccessWord (I := Option (Fin n)) M)
      = marketGridScan ω loss Δ q iT * (2*r+1) * (M-1) ∧
    marketGridScan ω loss Δ q iT * (2*r+1) * QueryCount (countedAECircuit M B j)
      = marketGridScan ω loss Δ q iT * (2*r+1) * (M-1) ∧
    marketGridScan ω loss Δ q iT * (2*r+1) * GateCount (countedAECircuit M B j)
      = marketGridScan ω loss Δ q iT * (2*r+1) * (5*(M-1)+3) := by
  exact risk_native_readout_charges B j M r (marketGridScan ω loss Δ q iT) hM

/-- Combines sample and comparison accounting with a scan bound and grid CDF failure probability
at most `(iT + 1) / (4 * N * ν ^ 2)`. -/
theorem marketGrid_cost_accuracy {n N : ℕ} (p : FinDist (Option (Fin n)))
    (ω : Fin N → Option (Fin n)) (loss : Option (Fin n) → ℝ) (Δ ν : ℝ) (iT : ℕ)
    (M r : ℕ) (hN : 0 < N) (hν : 0 < ν) :
    (marketProgramResources M r ω loss Δ ν iT).samples = N ∧
    (marketProgramResources M r ω loss Δ ν iT).tableReads ≤ iT + 1 ∧
    (marketProgramResources M r ω loss Δ ν iT).recordComparisons
      = (marketProgramResources M r ω loss Δ ν iT).tableReads * N ∧
    FinDist.probEvent (L := N) p (fun ω' : Fin N → Option (Fin n) =>
        ∃ j : Fin (iT+1),
          ν < |marketEmpiricalCDF ω' loss (gridThreshold Δ j.1)
            - marketCDF p loss (gridThreshold Δ j.1)|)
      ≤ ((iT+1 : ℝ))/(4*(N : ℝ)*ν^2) := by
  refine ⟨rfl, ?_, rfl, ?_⟩
  · exact marketGridScan_le ω loss Δ ν iT
  · exact marketGrid_uniform_sampling_bound p loss Δ ν iT hN hν
end Qatlib.Concepts.RiskEstimation.PopulationGap
