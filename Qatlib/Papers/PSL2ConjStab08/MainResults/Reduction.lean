/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Group.Subgroup.Lattice

/-!
# Restriction of subgroup-hiding oracles

Restricting a subgroup-hiding oracle to a subgroup replaces the hidden subgroup by its
intersection with that subgroup. The module records injectivity and distinctness conditions
ensuring that these intersections retain the original hidden-subgroup label, the reduction
principle used in [DenneyMooreRussell2008].

## Main statements

* `reduction_restriction_oracle`: restriction hides the subgroup intersection.
* `reduction_injective`: distinct intersections preserve an injective family of hidden
  subgroups.

## References

* [Denney et al., 2008][DenneyMooreRussell2008]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PSL2ConjStab08.MainResults.Reduction

variable {G γ : Type*} [Group G]

/-- If equality of oracle values is characterized by membership of `x⁻¹ * y` in `H`, then on `F`
it is characterized by membership in `H ⊓ F`. See [DenneyMooreRussell2008]. -/
theorem reduction_restriction_oracle (H F : Subgroup G) (f : G → γ)
    (hsep : ∀ x y : G, f x = f y ↔ x⁻¹ * y ∈ H) (x y : F) :
    f (x : G) = f (y : G) ↔ ((x⁻¹ * y : F) : G) ∈ H ⊓ F := by
  rw [hsep]
  constructor
  · intro h
    exact ⟨h, (x⁻¹ * y).2⟩
  · intro h
    exact h.1

/-- An injective family of subgroups remains injective after intersection with `F` if distinct
family members have distinct intersections. See [DenneyMooreRussell2008]. -/
theorem reduction_injective {ι : Type*} (H : ι → Subgroup G) (F : Subgroup G)
    (hH : Function.Injective H)
    (hd : ∀ i j, H i ≠ H j → H i ⊓ F ≠ H j ⊓ F) :
    Function.Injective fun i => H i ⊓ F := by
  intro i j hij
  by_contra hne
  exact hd i j (fun heq => hne (hH heq)) hij

/-- If distinct family members have distinct intersections with `F`, equal intersections imply
equal original subgroups. See [DenneyMooreRussell2008]. -/
theorem reduction_distinct_intersections {ι : Type*} (H : ι → Subgroup G)
    (F : Subgroup G) (hd : ∀ i j, H i ≠ H j → H i ⊓ F ≠ H j ⊓ F) :
    ∀ i j, H i ⊓ F = H j ⊓ F → H i = H j := by
  intro i j hij
  by_contra hne
  exact hd i j hne hij

end Qatlib.Papers.PSL2ConjStab08.MainResults.Reduction
