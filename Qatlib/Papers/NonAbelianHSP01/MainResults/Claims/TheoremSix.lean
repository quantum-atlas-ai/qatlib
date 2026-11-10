/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonAbelianHSP01.MainResults.Defs
import Qatlib.Papers.NonAbelianHSP01.MainResults.MembershipReduction
import Qatlib.Papers.NonAbelianHSP01.MainResults.Reductions
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Papers.NonAbelianHSP01.MainResults.Claims

open scoped IsMulCommutative

theorem theorem_six {M : Type*} [Group M] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → M) (hcomm : ∀ i j : ι, Commute (h i) (h j)) (g : M) :
    g ∈ Subgroup.closure (Set.range h) ↔
      ∃ (m : ι → ℤ) (n : ℤ),
        Nat.Coprime n.natAbs (orderOf g) ∧
          (zpowProd h hcomm m : M) * g ^ (-n) = 1 :=
  exists_coprime_kernel_iff h hcomm g

theorem theorem_six_oracles {G : Type*} [Group G] (B : BlackBoxGroupData G)
    (E : Encoding G) (_hE : E.Unique) : Nonempty (Oracles B) :=
  oracles_nonempty B

end Qatlib.Papers.NonAbelianHSP01.MainResults.Claims
