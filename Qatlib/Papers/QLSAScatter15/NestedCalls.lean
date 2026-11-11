/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLSAScatter15.ResourceReport.QlsaResourceDefs

/-!
# Nested oracle call resource model

The modeled constants combine Grover iterations, Hamiltonian simulation calls, Suzuki slices,
sparse terms, and kernel queries into `modeledOracleAQueries`. Exact arithmetic then compares
the modeled oracle volume with the resource ledger `tableII`. See [SchererEtAl2017] for the
paper context.

## Main statements

* `modeledOracleAQueries_eq`: The modeled Oracle A query count is exactly 265404600000000000000.
* `modeledOracleAVolume_dominates_total`: The modeled Oracle A volume lies in `[10^28, 10^29)`,
  bounds the total gate count within factors one and four, and bounds the total depth within
  factors one and three.
* `modeledOracleA_dominates_resource_count`: The modeled query count has order `10^20`, and
  including oracles increases both the ledger gate count and circuit depth by factors of at
  least 1000.

## References

* [Scherer et al., 2017][SchererEtAl2017]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QLSAScatter15.NestedCalls
open Qatlib.Papers.QLSAScatter15.ResourceReport

/-- The modeled number `2^14 - 1` of Grover iterations per subroutine. -/
def modeledGroverIteratorsPerSubroutine : ℕ := 2 ^ 14 - 1

/-- The modeled Hamiltonian simulation call count, equal to the Grover iteration count
multiplied by four and three. -/
def modeledHamiltonianSimulationCalls : ℕ := modeledGroverIteratorsPerSubroutine * 4 * 3

/-- The modeled Suzuki slice count `5^(k - 1)` per Trotter step. -/
def modeledSuzukiSlicesPerTrotterStep (k : ℕ) : ℕ := 5 ^ (k - 1)

/-- The chosen Suzuki parameter, equal to two. -/
def modeledSuzukiOrder : ℕ := 2

/-- The modeled Trotter splitting factor `25 * 10^11`. -/
def modeledTrotterSplittingFactor : ℕ := 25 * 10 ^ 11

/-- The modeled number `2 * 9` of one-sparse terms per band. -/
def modeledOneSparseTermsPerBand : ℕ := 2 * 9

/-- The modeled number of Oracle A queries per kernel, equal to six. -/
def modeledOracleAQueriesPerKernel : ℕ := 6

/-- The modeled Oracle A query count obtained by multiplying kernel queries, sparse terms,
simulation calls, Trotter splitting, and Suzuki slices. -/
def modeledOracleAQueries : ℕ :=
  modeledOracleAQueriesPerKernel * modeledOneSparseTermsPerBand *
    (modeledHamiltonianSimulationCalls * modeledTrotterSplittingFactor *
      modeledSuzukiSlicesPerTrotterStep modeledSuzukiOrder)

/-- The modeled number of Grover iterations per subroutine is 16383. -/
theorem modeledGroverIteratorsPerSubroutine_eq : modeledGroverIteratorsPerSubroutine = 16383 := by
  norm_num [modeledGroverIteratorsPerSubroutine]

/-- The modeled Hamiltonian simulation call count is 196596. -/
theorem modeledHamiltonianSimulationCalls_eq : modeledHamiltonianSimulationCalls = 196596 := by
  norm_num [modeledHamiltonianSimulationCalls, modeledGroverIteratorsPerSubroutine]

/-- At Suzuki parameter two, the modeled slice count per Trotter step is five. See
[SchererEtAl2017]. -/
theorem modeledSuzukiSlicesPerTrotterStep_two : modeledSuzukiSlicesPerTrotterStep 2 = 5 := by
  norm_num [modeledSuzukiSlicesPerTrotterStep]

/-- The modeled Oracle A query count is exactly 265404600000000000000. See [SchererEtAl2017]. -/
theorem modeledOracleAQueries_eq : modeledOracleAQueries = 265404600000000000000 := by
  norm_num [modeledOracleAQueries, modeledOracleAQueriesPerKernel, modeledOneSparseTermsPerBand,
    modeledHamiltonianSimulationCalls, modeledGroverIteratorsPerSubroutine,
    modeledTrotterSplittingFactor, modeledSuzukiSlicesPerTrotterStep, modeledSuzukiOrder]

/-- The modeled Oracle A query count lies in the interval from `10^20` inclusive to `10^21`
exclusive. See [SchererEtAl2017]. -/
theorem modeledOracleAQueries_order : OrderOfMagnitude 20 modeledOracleAQueries := by
  rw [modeledOracleAQueries_eq]
  norm_num [OrderOfMagnitude]

/-- The modeled Oracle A volume per query, equal to `25 * 10^7`. -/
def modeledOracleAVolumePerQuery : ℕ := 25 * 10 ^ 7

/-- The product of the modeled Oracle A query count and volume per query. -/
def modeledOracleATotalVolume : ℕ := modeledOracleAQueries * modeledOracleAVolumePerQuery

/-- The modeled total Oracle A volume is exactly 66351150000000000000000000000. See
[SchererEtAl2017]. -/
theorem modeledOracleATotalVolume_eq :
    modeledOracleATotalVolume = 66351150000000000000000000000 := by
  norm_num [modeledOracleATotalVolume, modeledOracleAQueries, modeledOracleAQueriesPerKernel,
    modeledOneSparseTermsPerBand, modeledHamiltonianSimulationCalls,
    modeledGroverIteratorsPerSubroutine, modeledTrotterSplittingFactor,
    modeledSuzukiSlicesPerTrotterStep, modeledSuzukiOrder, modeledOracleAVolumePerQuery]

/-- The modeled Oracle A volume lies in `[10^28, 10^29)`, bounds the total gate count within
factors one and four, and bounds the total depth within factors one and three. See
[SchererEtAl2017]. -/
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

/-- The modeled query count has order `10^20`, and including oracles increases both the ledger
gate count and circuit depth by factors of at least 1000. See [SchererEtAl2017]. -/
theorem modeledOracleA_dominates_resource_count :
    OrderOfMagnitude 20 modeledOracleAQueries ∧
    10 ^ 3 * tableII.gateCountExclOracles ≤ tableII.gateCountInclOracles ∧
    10 ^ 3 * tableII.circuitDepthExclOracles ≤ tableII.circuitDepthInclOracles := by
  refine ⟨modeledOracleAQueries_order, ?_, ?_⟩ <;> norm_num [tableII]

end Qatlib.Papers.QLSAScatter15.NestedCalls
