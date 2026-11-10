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

theorem theorem_seven_test {G : Type*} [Group G] {X : Type*} (N : Subgroup G)
    [N.Normal] (I : HiddenSubgroupInstance G X) (hN : I.H = N) (y : G) :
    I.f y = I.f 1 ↔ (y : G ⧸ N) = 1 :=
  f_eq_one_iff_quotient_eq_one (N := N) I.f (fun a b => by rw [I.hides, hN]) y

theorem theorem_seven {G : Type*} [Group G] {X : Type*} (N : Subgroup G)
    [N.Normal] (I : HiddenSubgroupInstance G X) (hN : I.H = N)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (h : ι → G) (g : G)
    (hcomm : ∀ i j : ι, Commute ((h i : G ⧸ N)) ((h j : G ⧸ N))) :
    ((g : G ⧸ N) ∈ Subgroup.closure (Set.range (fun i => (h i : G ⧸ N))) ↔
        ∃ (m : ι → ℤ) (n : ℤ),
          Nat.Coprime n.natAbs (orderOf ((g : G ⧸ N))) ∧
            (zpowProd (fun i => (h i : G ⧸ N)) hcomm m : G ⧸ N) *
              (g : G ⧸ N) ^ (-n) = 1) ∧
      (I.f g = I.f 1 ↔ (g : G ⧸ N) = 1) :=
  ⟨quotient_membership_iff h g hcomm, theorem_seven_test N I hN g⟩

end Qatlib.Papers.NonAbelianHSP01.MainResults.Claims
