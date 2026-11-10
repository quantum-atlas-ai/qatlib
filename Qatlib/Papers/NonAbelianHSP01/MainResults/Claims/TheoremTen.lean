/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonAbelianHSP01.MainResults.Defs
import Qatlib.Papers.NonAbelianHSP01.MainResults.MembershipReduction
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Papers.NonAbelianHSP01.MainResults.Claims

theorem theorem_ten {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (g : G) (k : ℕ) :
    ((g : G ⧸ N) ^ k = 1 ↔ g ^ k ∈ N) ∧
      ((g : G ⧸ N) ^ k = 1 ↔ orderOf ((g : G ⧸ N)) ∣ k) :=
  ⟨order_in_quotient_eq_period g k, order_in_quotient_dvd_iff g k⟩

end Qatlib.Papers.NonAbelianHSP01.MainResults.Claims
