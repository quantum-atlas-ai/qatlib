/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonAbelianHSP01.MainResults.Defs
import Qatlib.Papers.NonAbelianHSP01.MainResults.ElementaryAbelianTwo
import Qatlib.Papers.NonAbelianHSP01.MainResults.Reductions

/-!
# Coset reductions for elementary abelian two subgroups

Bundles coset-intersection and subgroup-reconstruction identities in the presence of a normal
subgroup satisfying `IsElementaryAbelianTwo`. The result `theorem_thirteen` also records that
every element of that subgroup is its own inverse. See [IvanyosMagniezSantha2003] for the
surrounding analysis.

## Main statements

* `theorem_thirteen`: For normal elementary abelian two `N`, the stated coset intersections are
  empty or cosets of `I.H ⊓ N`, their representatives yield elements of `I.H` and the displayed
  translate identity, and the join/intersection hypotheses reconstruct `I.H`. Every element of
  `N` is also its own inverse.

## References

* [Ivanyos et al., 2003][IvanyosMagniezSantha2003]
-/

set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Papers.NonAbelianHSP01.MainResults.Claims

/-- For normal elementary abelian two `N`, the stated coset intersections are empty or cosets of
`I.H ⊓ N`, their representatives yield elements of `I.H` and the displayed translate
identity, and the join/intersection hypotheses reconstruct `I.H`. Every element of `N` is
also its own inverse [IvanyosMagniezSantha2003]. -/
theorem theorem_thirteen {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    {X : Type*} (I : HiddenSubgroupInstance G X) (hNtwo : IsElementaryAbelianTwo ↥N) :
    (∀ z : G, leftCoset z I.H ∩ (N : Set G) = ∅ ∨
        ∃ u : G, u ∈ leftCoset z I.H ∩ (N : Set G) ∧
          leftCoset z I.H ∩ (N : Set G) = leftCoset u (I.H ⊓ N)) ∧
      (∀ z u : G, u ∈ leftCoset z I.H ∩ (N : Set G) → u⁻¹ * z ∈ I.H) ∧
      (∀ z u : G, u ∈ leftCoset z I.H ∩ (N : Set G) →
        ((fun n : G => z * n) '' (N : Set G)) ∩ (I.H : Set G) =
          ((fun k : G => (u⁻¹ * z) * k) '' ((I.H ⊓ N : Subgroup G) : Set G))) ∧
      (∀ H₁ : Subgroup G, H₁ ≤ I.H → I.H ⊓ N ≤ H₁ → H₁ ⊔ N = I.H ⊔ N → H₁ = I.H) ∧
      (∀ x : ↥N, x⁻¹ = x) :=
  ⟨fun z => coset_inter_normal_eq_empty_or_coset (H := I.H) (N := N) z,
    fun _ _ hu => inv_mul_mem_of_mem_leftCoset_inter hu,
    fun z u hu => rightCoset_inter_eq_image z u hu,
    fun H₁ hle hHN hsup => theorem_thirteen_reduction hle hHN hsup,
    fun x => hNtwo.inv_eq_self x⟩

end Qatlib.Papers.NonAbelianHSP01.MainResults.Claims
