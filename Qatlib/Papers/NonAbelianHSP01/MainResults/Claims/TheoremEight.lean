/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonAbelianHSP01.MainResults.Defs
import Qatlib.Papers.NonAbelianHSP01.MainResults.HiddenNormalSubgroup

/-!
# Normal closure recognition by index

Combines recognition of a normal subgroup from containment and equal finite index with the
identity-fiber description of a hiding function. The theorem `theorem_eight` states these
algebraic conclusions under the given index hypotheses. See [IvanyosMagniezSantha2003] for the
surrounding analysis.

## Main statements

* `theorem_eight`: If the normal closure of `s` lies in `N` and has the same nonzero index as
  `N`, it equals `N`; every hidden-subgroup instance hiding `N` also identifies its hidden
  subgroup with the identity fiber.

## References

* [Ivanyos et al., 2003][IvanyosMagniezSantha2003]
-/

set_option autoImplicit false

namespace Qatlib.Papers.NonAbelianHSP01.MainResults.Claims

/-- If the normal closure of `s` lies in `N` and has the same nonzero index as `N`, it equals
`N`; every hidden-subgroup instance hiding `N` also identifies its hidden subgroup with the
identity fiber [IvanyosMagniezSantha2003]. -/
theorem theorem_eight {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (s : Set G) (hle : Subgroup.normalClosure s ≤ N) (hN : N.index ≠ 0)
    (hidx : (Subgroup.normalClosure s).index = N.index) :
    Subgroup.normalClosure s = N ∧
      (∀ {X : Type*} (I : HiddenSubgroupInstance G X), I.H = N →
        I.H = {a : G | I.f a = I.f 1}) :=
  ⟨normalClosure_eq_of_index_eq hle hN hidx,
    fun I _ => hidden_normal_eq_stabilizer I⟩

end Qatlib.Papers.NonAbelianHSP01.MainResults.Claims
