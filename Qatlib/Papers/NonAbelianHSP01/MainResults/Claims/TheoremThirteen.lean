/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonAbelianHSP01.MainResults.Defs
import Qatlib.Papers.NonAbelianHSP01.MainResults.ElementaryAbelianTwo
import Qatlib.Papers.NonAbelianHSP01.MainResults.Reductions
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Papers.NonAbelianHSP01.MainResults.Claims

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
