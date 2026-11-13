/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonAbelianHSP01.MainResults.Defs
import Qatlib.Papers.NonAbelianHSP01.MainResults.MembershipReduction

/-!
# Orders and periods in normal quotients

Collects two descriptions of powers that become the identity in a normal quotient. The result
`theorem_ten` expresses the condition both as subgroup membership and as divisibility by the
quotient element's order. See [IvanyosMagniezSantha2003] for the surrounding analysis.

## Main statements

* `theorem_ten`: The `k`th power of the image of `g` in `G ⧸ N` is the identity exactly when `g
  ^ k ∈ N`, and exactly when `orderOf (g : G ⧸ N)` divides `k`.

## References

* [Ivanyos et al., 2003][IvanyosMagniezSantha2003]
-/

set_option autoImplicit false

namespace Qatlib.Papers.NonAbelianHSP01.MainResults.Claims

/-- The `k`th power of the image of `g` in `G ⧸ N` is the identity exactly when `g ^ k ∈ N`, and
exactly when `orderOf (g : G ⧸ N)` divides `k` [IvanyosMagniezSantha2003]. -/
theorem theorem_ten {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (g : G) (k : ℕ) :
    ((g : G ⧸ N) ^ k = 1 ↔ g ^ k ∈ N) ∧
      ((g : G ⧸ N) ^ k = 1 ↔ orderOf ((g : G ⧸ N)) ∣ k) :=
  ⟨order_in_quotient_eq_period g k, order_in_quotient_dvd_iff g k⟩

end Qatlib.Papers.NonAbelianHSP01.MainResults.Claims
