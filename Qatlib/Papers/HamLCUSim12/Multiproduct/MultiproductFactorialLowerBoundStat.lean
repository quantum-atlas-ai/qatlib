/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductAnalyticInputs

/-!
# Factorial lower-bound statement

The proposition `MultiproductFactorialLowerBound` names `FactorialLowerBound` as a standalone
analytic input. It expresses an explicit Stirling-type lower estimate used to control the
factorial denominators in multiproduct coefficients. See [ChildsWiebe2012] for the multiproduct
and linear-combination simulation framework.

## Main statements

* `MultiproductFactorialLowerBound`: An alias for `FactorialLowerBound`, asserting √(2πn) n^n
  exp(−n − 1 / 13) ≤ n! for all natural numbers n.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

set_option warningAsError false
set_option autoImplicit false

namespace Qatlib.Papers.HamLCUSim12.Multiproduct

/-- An alias for `FactorialLowerBound`, asserting √(2πn) n^n exp(−n − 1 / 13) ≤ n! for all
natural numbers n. -/
def MultiproductFactorialLowerBound : Prop := FactorialLowerBound

end Qatlib.Papers.HamLCUSim12.Multiproduct
