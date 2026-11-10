/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLSAScatter15.ResourceReport.QlsaResourceDefs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QLSAScatter15.NestedCalls
open Qatlib.Papers.QLSAScatter15.ResourceReport

def modeledGroverIteratorsPerSubroutine : ℕ := 2 ^ 14 - 1

def modeledHamiltonianSimulationCalls : ℕ := modeledGroverIteratorsPerSubroutine * 4 * 3

def modeledSuzukiSlicesPerTrotterStep (k : ℕ) : ℕ := 5 ^ (k - 1)

def modeledSuzukiOrder : ℕ := 2

def modeledTrotterSplittingFactor : ℕ := 25 * 10 ^ 11

def modeledOneSparseTermsPerBand : ℕ := 2 * 9

def modeledOracleAQueriesPerKernel : ℕ := 6

def modeledOracleAQueries : ℕ :=
  modeledOracleAQueriesPerKernel * modeledOneSparseTermsPerBand *
    (modeledHamiltonianSimulationCalls * modeledTrotterSplittingFactor *
      modeledSuzukiSlicesPerTrotterStep modeledSuzukiOrder)

theorem modeledGroverIteratorsPerSubroutine_eq : modeledGroverIteratorsPerSubroutine = 16383 := by
  norm_num [modeledGroverIteratorsPerSubroutine]

theorem modeledHamiltonianSimulationCalls_eq : modeledHamiltonianSimulationCalls = 196596 := by
  norm_num [modeledHamiltonianSimulationCalls, modeledGroverIteratorsPerSubroutine]

theorem modeledSuzukiSlicesPerTrotterStep_two : modeledSuzukiSlicesPerTrotterStep 2 = 5 := by
  norm_num [modeledSuzukiSlicesPerTrotterStep]

theorem modeledOracleAQueries_eq : modeledOracleAQueries = 265404600000000000000 := by
  norm_num [modeledOracleAQueries, modeledOracleAQueriesPerKernel, modeledOneSparseTermsPerBand,
    modeledHamiltonianSimulationCalls, modeledGroverIteratorsPerSubroutine,
    modeledTrotterSplittingFactor, modeledSuzukiSlicesPerTrotterStep, modeledSuzukiOrder]

theorem modeledOracleAQueries_order : OrderOfMagnitude 20 modeledOracleAQueries := by
  rw [modeledOracleAQueries_eq]
  norm_num [OrderOfMagnitude]

def modeledOracleAVolumePerQuery : ℕ := 25 * 10 ^ 7

def modeledOracleATotalVolume : ℕ := modeledOracleAQueries * modeledOracleAVolumePerQuery

theorem modeledOracleATotalVolume_eq :
    modeledOracleATotalVolume = 66351150000000000000000000000 := by
  norm_num [modeledOracleATotalVolume, modeledOracleAQueries, modeledOracleAQueriesPerKernel,
    modeledOneSparseTermsPerBand, modeledHamiltonianSimulationCalls,
    modeledGroverIteratorsPerSubroutine, modeledTrotterSplittingFactor,
    modeledSuzukiSlicesPerTrotterStep, modeledSuzukiOrder, modeledOracleAVolumePerQuery]

theorem modeledOracleAVolume_dominates_total :
    10 ^ 28 ≤ modeledOracleATotalVolume ∧ modeledOracleATotalVolume < 10 ^ 29 ∧
    modeledOracleATotalVolume ≤ tableII.gateCountInclOracles ∧
    tableII.gateCountInclOracles ≤ 4 * modeledOracleATotalVolume ∧
    modeledOracleATotalVolume ≤ tableII.circuitDepthInclOracles ∧
    tableII.circuitDepthInclOracles ≤ 3 * modeledOracleATotalVolume := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [modeledOracleATotalVolume, modeledOracleAQueries, modeledOracleAQueriesPerKernel,
      modeledOneSparseTermsPerBand, modeledHamiltonianSimulationCalls,
      modeledGroverIteratorsPerSubroutine, modeledTrotterSplittingFactor,
      modeledSuzukiSlicesPerTrotterStep, modeledSuzukiOrder, modeledOracleAVolumePerQuery, tableII]

theorem modeledOracleA_dominates_resource_count :
    OrderOfMagnitude 20 modeledOracleAQueries ∧
    10 ^ 3 * tableII.gateCountExclOracles ≤ tableII.gateCountInclOracles ∧
    10 ^ 3 * tableII.circuitDepthExclOracles ≤ tableII.circuitDepthInclOracles := by
  refine ⟨modeledOracleAQueries_order, ?_, ?_⟩ <;> norm_num [tableII]

end Qatlib.Papers.QLSAScatter15.NestedCalls
