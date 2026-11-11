/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductNodes

/-!
# Multiproduct coefficient sign-structure statement

The proposition `MultiproductMassStructure` records two features of the multiproduct
coefficients when N > k ≥ 1. The terminal coefficient is at least 1, and the coefficient family
contains a negative entry. See [ChildsWiebe2012] for the multiproduct and linear-combination
simulation framework.

## Main statements

* `MultiproductMassStructure`: The proposition that the terminal coefficient is at least 1 and
  some coefficient is negative for every k ≥ 1 and N > k.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

set_option autoImplicit false
namespace Qatlib.Papers.HamLCUSim12.Multiproduct
open scoped BigOperators

/-- The proposition that the terminal coefficient is at least 1 and some coefficient is negative
for every k ≥ 1 and N > k. -/
def MultiproductMassStructure : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ N : ℝ, (k : ℝ) < N →
    1 ≤ mCoeff k N (Fin.last k) ∧ ∃ q : Fin (k+1), mCoeff k N q < 0

end Qatlib.Papers.HamLCUSim12.Multiproduct
