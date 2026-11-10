/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonAbelianHSP01.MainResults.Defs
import Qatlib.Papers.NonAbelianHSP01.MainResults.HiddenNormalSubgroup
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Papers.NonAbelianHSP01.MainResults.Claims

theorem theorem_eight {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (s : Set G) (hle : Subgroup.normalClosure s ≤ N) (hN : N.index ≠ 0)
    (hidx : (Subgroup.normalClosure s).index = N.index) :
    Subgroup.normalClosure s = N ∧
      (∀ {X : Type*} (I : HiddenSubgroupInstance G X), I.H = N →
        I.H = {a : G | I.f a = I.f 1}) :=
  ⟨normalClosure_eq_of_index_eq hle hN hidx,
    fun I _ => hidden_normal_eq_stabilizer I⟩

end Qatlib.Papers.NonAbelianHSP01.MainResults.Claims
