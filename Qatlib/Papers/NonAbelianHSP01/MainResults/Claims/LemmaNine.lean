/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonAbelianHSP01.MainResults.Defs
import Qatlib.Papers.NonAbelianHSP01.MainResults.AbelianHSP
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Papers.NonAbelianHSP01.MainResults.Claims

open scoped IsMulCommutative

theorem lemma_nine {G : Type*} [Group G] [IsMulCommutative G] {X : Type*}
    (I : HiddenSubgroupInstance G X) :
    I.H.Normal ∧
      I.H = {a : G | ∀ x : G, I.f (x * a) = I.f x} ∧
      (∀ (I' : HiddenSubgroupInstance G X), (∀ a : G, I'.f a = I.f a) →
        I'.H = I.H) :=
  ⟨hidden_subgroup_normal_of_commutative I,
    hidden_subgroup_eq_right_stabilizer I,
    fun I' h => hidden_subgroup_determined_by_hiding_values I I' h⟩

end Qatlib.Papers.NonAbelianHSP01.MainResults.Claims
