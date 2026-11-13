/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLSAScatter15.ResourceReport.QlsaResourceDefs

/-!
# Verification of the QLSA resource ledger

This module checks the recorded `tableII` resource estimates by exact arithmetic. The results
establish the specified orders of magnitude and show that including oracles increases width,
depth, and gate count by factors of at least 1000. See [SchererEtAl2017] for the paper context.

## Main statements

* `tableII_matches_published_estimates`: The ledger has width 341 and depth of order `10^25`
  without oracles, and width of order `10^8` and depth of order `10^29` including oracles, with
  width and depth increased by factors of at least 1000.
* `oracle_resources_considerable`: Including oracles increases each of the ledger's circuit
  width, depth, and gate count by a factor of at least 1000.

## References

* [Scherer et al., 2017][SchererEtAl2017]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QLSAScatter15.ResourceReport

/-- The ledger has width 341 and depth of order `10^25` without oracles, and width of order
`10^8` and depth of order `10^29` including oracles, with width and depth increased by
factors of at least 1000. See [SchererEtAl2017]. -/
theorem tableII_matches_published_estimates :
    tableII.circuitWidthExclOracles = 341 ∧
    340 ≤ tableII.circuitWidthExclOracles ∧
    tableII.circuitWidthExclOracles ≤ 341 ∧
    OrderOfMagnitude 25 tableII.circuitDepthExclOracles ∧
    OrderOfMagnitude 8 tableII.circuitWidthInclOracles ∧
    OrderOfMagnitude 29 tableII.circuitDepthInclOracles ∧
    10 ^ 3 * tableII.circuitWidthExclOracles ≤ tableII.circuitWidthInclOracles ∧
    10 ^ 3 * tableII.circuitDepthExclOracles ≤ tableII.circuitDepthInclOracles := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [tableII, OrderOfMagnitude]

/-- Including oracles increases each of the ledger's circuit width, depth, and gate count by a
factor of at least 1000. See [SchererEtAl2017]. -/
theorem oracle_resources_considerable :
    10 ^ 3 * tableII.circuitWidthExclOracles ≤ tableII.circuitWidthInclOracles ∧
    10 ^ 3 * tableII.circuitDepthExclOracles ≤ tableII.circuitDepthInclOracles ∧
    10 ^ 3 * tableII.gateCountExclOracles ≤ tableII.gateCountInclOracles := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [tableII]

end Qatlib.Papers.QLSAScatter15.ResourceReport
