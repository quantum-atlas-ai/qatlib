/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonAbelianHSP01.MainResults.Defs
import Qatlib.Papers.NonAbelianHSP01.MainResults.CommutatorExtraSpecial
import Qatlib.Papers.NonAbelianHSP01.MainResults.Reductions
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Papers.NonAbelianHSP01.MainResults.Claims

open scoped IsMulCommutative

theorem corollary_twelve {G : Type*} [Group G] (B : BlackBoxGroupData G) {p : ℕ}
    (hp : IsExtraSpecial p G) {X : Type*} (I : HiddenSubgroupInstance G X)
    (S : Finset G) (hS : Subgroup.closure (S : Set G) = I.H ⊔ commutator G)
    (T : Finset G) (hT : Subgroup.closure (T : Set G) = I.H ⊓ commutator G)
    (u : G → G) (hu_mem : ∀ x ∈ (S : Set G), u x ∈ I.H)
    (hu_eq : ∀ x ∈ (S : Set G), ∃ n ∈ commutator G, u x * n = x)
    (costS : CostLedger) (hcost : PolyBoundedIn B p costS) :
    (Nat.card (Subgroup.center G) = p ∧ IsMulCommutative (G ⧸ commutator G)) ∧
      ∃ s : HiddenSubgroupSolution B I, PolyBoundedIn B p s.cost := by
  have hcard : Nat.card (commutator G) = p := hp.card_commutator
  obtain ⟨s, hs⟩ :=
    theorem_eleven_reduction (G := G) B I S hS T hT u hu_mem hu_eq costS
      (hcard.symm ▸ hcost)
  exact ⟨⟨hp.card_center, hp.quotient_commutative⟩, ⟨s, by simpa only [hcard] using hs⟩⟩

end Qatlib.Papers.NonAbelianHSP01.MainResults.Claims
