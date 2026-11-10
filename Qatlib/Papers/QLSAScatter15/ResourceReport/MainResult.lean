/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLSAScatter15.ResourceReport.QlsaResourceDefs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QLSAScatter15.ResourceReport

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

theorem oracle_resources_considerable :
    10 ^ 3 * tableII.circuitWidthExclOracles ≤ tableII.circuitWidthInclOracles ∧
    10 ^ 3 * tableII.circuitDepthExclOracles ≤ tableII.circuitDepthInclOracles ∧
    10 ^ 3 * tableII.gateCountExclOracles ≤ tableII.gateCountInclOracles := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [tableII]

end Qatlib.Papers.QLSAScatter15.ResourceReport
