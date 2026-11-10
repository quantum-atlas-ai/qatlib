/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Group.Subgroup.Lattice

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PSL2ConjStab08.MainResults.Reduction

variable {G γ : Type*} [Group G]

theorem reduction_restriction_oracle (H F : Subgroup G) (f : G → γ)
    (hsep : ∀ x y : G, f x = f y ↔ x⁻¹ * y ∈ H) (x y : F) :
    f (x : G) = f (y : G) ↔ ((x⁻¹ * y : F) : G) ∈ H ⊓ F := by
  rw [hsep]
  constructor
  · intro h
    exact ⟨h, (x⁻¹ * y).2⟩
  · intro h
    exact h.1

theorem reduction_injective {ι : Type*} (H : ι → Subgroup G) (F : Subgroup G)
    (hH : Function.Injective H)
    (hd : ∀ i j, H i ≠ H j → H i ⊓ F ≠ H j ⊓ F) :
    Function.Injective fun i => H i ⊓ F := by
  intro i j hij
  by_contra hne
  exact hd i j (fun heq => hne (hH heq)) hij

theorem reduction_distinct_intersections {ι : Type*} (H : ι → Subgroup G)
    (F : Subgroup G) (hd : ∀ i j, H i ≠ H j → H i ⊓ F ≠ H j ⊓ F) :
    ∀ i j, H i ⊓ F = H j ⊓ F → H i = H j := by
  intro i j hij
  by_contra hne
  exact hd i j hne hij

end Qatlib.Papers.PSL2ConjStab08.MainResults.Reduction
