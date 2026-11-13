/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductCoefficientAux
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductCoefficientDiagnostics

/-!
# Sign structure of multiproduct coefficients

This module proves `multiproductMassStructure` for terminal nodes N > k ≥ 1. It combines the
lower bound on the final coefficient with the strict negativity of the penultimate coefficient.
See [ChildsWiebe2012] for the multiproduct and linear-combination simulation framework.

## Main statements

* `multiproductMassStructure`: For k ≥ 1 and N > k, the final multiproduct coefficient is at
  least 1 and at least one coefficient is negative.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

set_option autoImplicit false
namespace Qatlib.Papers.HamLCUSim12.Multiproduct

/-- For k ≥ 1 and N > k, the final multiproduct coefficient is at least 1 and at least one
coefficient is negative. See [ChildsWiebe2012]. -/
theorem multiproductMassStructure : MultiproductMassStructure := by
  intro k hk N hN
  exact ⟨multiproduct_last_coefficient_ge_one k hk N hN,
    ⟨⟨k-1, by omega⟩, multiproduct_penultimate_negative k hk N hN⟩⟩

end Qatlib.Papers.HamLCUSim12.Multiproduct
