/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonAbelianHSP01.MainResults.Defs
import Qatlib.Papers.NonAbelianHSP01.MainResults.CommutatorExtraSpecial
import Qatlib.Papers.NonAbelianHSP01.MainResults.Reductions

/-!
# Algebraic specialization of hidden-subgroup reconstruction

The result below reconstructs a generating set from supplied generators and
lifts. It provides no oracle implementation and assigns no execution cost.
-/

set_option autoImplicit false

namespace Qatlib.Papers.NonAbelianHSP01.MainResults.Claims

open scoped IsMulCommutative

/-- **Statement only — not proved in Qatlib.**
Legacy ledger-level output target for Corollary 12. No oracle program is
specified by this predicate. The separate theorem below proves only the
group identities and reconstruction from supplied generators and lifts. -/
def corollary_twelve_statement {G : Type*} [Group G] (B : BlackBoxGroupData G) {p : ℕ}
    (_hp : IsExtraSpecial p G) {X : Type*} (I : HiddenSubgroupInstance G X)
    (S : Finset G) (_hS : Subgroup.closure (S : Set G) = I.H ⊔ commutator G)
    (T : Finset G) (_hT : Subgroup.closure (T : Set G) = I.H ⊓ commutator G)
    (u : G → G) (_hu_mem : ∀ x ∈ (S : Set G), u x ∈ I.H)
    (_hu_eq : ∀ x ∈ (S : Set G), ∃ n ∈ commutator G, u x * n = x)
    (costS : CostLedger) (_hcost : PolyBoundedIn B p costS) : Prop :=
    (Nat.card (Subgroup.center G) = p ∧ IsMulCommutative (G ⧸ commutator G)) ∧
      ∃ s : HiddenSubgroupSolution B I, PolyBoundedIn B p s.cost

/-- Algebraic reconstruction from supplied data, without a complexity claim. -/
theorem corollary_twelve_algebraic {G : Type*} [Group G] (_B : BlackBoxGroupData G) {p : ℕ}
    (hp : IsExtraSpecial p G) {X : Type*} (I : HiddenSubgroupInstance G X)
    (S : Finset G) (hS : Subgroup.closure (S : Set G) = I.H ⊔ commutator G)
    (T : Finset G) (hT : Subgroup.closure (T : Set G) = I.H ⊓ commutator G)
    (u : G → G) (hu_mem : ∀ x ∈ (S : Set G), u x ∈ I.H)
    (hu_eq : ∀ x ∈ (S : Set G), ∃ n ∈ commutator G, u x * n = x)
    : (Nat.card (Subgroup.center G) = p ∧ IsMulCommutative (G ⧸ commutator G)) ∧
      ∃ R : Finset G, Subgroup.closure (R : Set G) = I.H := by
  exact ⟨⟨hp.card_center, hp.quotient_commutative⟩,
    theorem_eleven_reduction_generators I S hS T hT u hu_mem hu_eq⟩

end Qatlib.Papers.NonAbelianHSP01.MainResults.Claims
