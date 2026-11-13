/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductAnalyticInputs

/-!
# Certified scalar-maximum existence statement

The proposition `MultiproductEtaRecord` asks for a bound η in (0.305, 0.312) satisfying
`EtaMaxProperty`. It packages the numerical scalar estimate needed to certify the multiproduct
coefficient bounds. See [ChildsWiebe2012] for the multiproduct and linear-combination simulation
framework.

## Main statements

* `MultiproductEtaRecord`: The proposition that some real η with 0.305 < η < 0.312 satisfies
  `EtaMaxProperty`.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

set_option autoImplicit false

namespace Qatlib.Papers.HamLCUSim12.Multiproduct

/-- The proposition that some real η with 0.305 < η < 0.312 satisfies `EtaMaxProperty`. -/
def MultiproductEtaRecord : Prop :=
  ∃ η : ℝ, 305 / 1000 < η ∧ η < 312 / 1000 ∧ EtaMaxProperty η

end Qatlib.Papers.HamLCUSim12.Multiproduct
