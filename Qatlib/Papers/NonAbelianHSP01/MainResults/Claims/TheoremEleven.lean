/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonAbelianHSP01.MainResults.Defs
import Qatlib.Papers.NonAbelianHSP01.MainResults.Reductions
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Papers.NonAbelianHSP01.MainResults.Claims

theorem theorem_eleven {G : Type*} [Group G] (B : BlackBoxGroupData G)
    {X : Type*} (I : HiddenSubgroupInstance G X)
    (S : Finset G) (hS : Subgroup.closure (S : Set G) = I.H ⊔ commutator G)
    (T : Finset G) (hT : Subgroup.closure (T : Set G) = I.H ⊓ commutator G)
    (u : G → G) (hu_mem : ∀ x ∈ (S : Set G), u x ∈ I.H)
    (hu_eq : ∀ x ∈ (S : Set G), ∃ n ∈ commutator G, u x * n = x)
    (costS : CostLedger)
    (hcostS : PolyBoundedIn B (Nat.card (commutator G)) costS) :
    ∃ s : HiddenSubgroupSolution B I,
      PolyBoundedIn B (Nat.card (commutator G)) s.cost :=
  theorem_eleven_reduction B I S hS T hT u hu_mem hu_eq costS hcostS

end Qatlib.Papers.NonAbelianHSP01.MainResults.Claims
