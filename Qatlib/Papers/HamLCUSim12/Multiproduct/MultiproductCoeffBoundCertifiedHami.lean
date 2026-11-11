/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductCoeffBoundCertifiedStat
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductEtaRecordHami
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductFactorialLowerBoundHami
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductCoeffBoundHami

/-!
# Certified multiproduct coefficient bound

This module proves `multiproductCoeffBoundCertified`, supplying a coefficient bound with a
certified η between 0.305 and 0.312. The estimate applies to the first k multiproduct
coefficients when k ≥ 1, γ > 0, and the terminal node satisfies the required separation
inequality. See [ChildsWiebe2012] for the multiproduct and linear-combination simulation
framework.

## Main statements

* `multiproductCoeffBoundCertified`: Establishes the existence of 0.305 < η < 0.312 giving the
  uniform first-k coefficient estimate in `MultiproductCoeffBoundCertified`.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

set_option warningAsError false
set_option autoImplicit false
namespace Qatlib.Papers.HamLCUSim12.Multiproduct

/-- Establishes the existence of 0.305 < η < 0.312 giving the uniform first-k coefficient
estimate in `MultiproductCoeffBoundCertified`. See [ChildsWiebe2012]. -/
theorem multiproductCoeffBoundCertified : MultiproductCoeffBoundCertified := by
  obtain ⟨η, hlo, hhi, hE⟩ := multiproductEtaRecord
  refine ⟨η, hlo, hhi, ?_⟩
  intro k hk γ hγ hc q hq
  exact multiproductCoeffBound k hk γ η hγ (by linarith) hE
    multiproductFactorialLowerBound hc q hq

end Qatlib.Papers.HamLCUSim12.Multiproduct
