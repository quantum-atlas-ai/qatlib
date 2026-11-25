/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QSolvableGrp00.MainResults.Membership

@[expose] public section

/-!
# Solvability when adjoining a candidate element

The membership reduction in Section 4.1 may reject as soon as the enlarged
subgroup is not solvable. A member of the original subgroup would leave its
generated subgroup identical under adjoining.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QSolvableGrp00.MainResults

/-- Adjoining a candidate that makes the generated subgroup nonsolvable certifies nonmembership. -/
theorem adjoin_not_mem {G : Type*} [Group G] [DecidableEq G] (s : Finset G) (x : G)
    (hsol : Group.IsSolvable ↥(Subgroup.closure (s : Set G)))
    (hfail : ¬ Group.IsSolvable ↥(Subgroup.closure ((s ∪ {x} : Finset G) : Set G))) :
    x ∉ Subgroup.closure (s : Set G) := by
  intro hx
  have hle : Subgroup.closure ((s ∪ {x} : Finset G) : Set G) ≤ Subgroup.closure (s : Set G) := by
    apply (Subgroup.closure_le (k := ((s ∪ {x} : Finset G) : Set G))
      (K := Subgroup.closure (s : Set G))).mpr
    intro y hy
    rw [Finset.coe_union, Finset.coe_singleton, Set.mem_union, Set.mem_singleton_iff] at hy
    rcases hy with hy | rfl
    · exact Subgroup.subset_closure hy
    · exact hx
  have heq := le_antisymm hle (Subgroup.closure_mono
    (show (s : Set G) ⊆ ((s ∪ {x} : Finset G) : Set G) from fun _ h => Finset.mem_union_left _ h))
  exact hfail (heq.symm ▸ hsol)

end Qatlib.Papers.QSolvableGrp00.MainResults
