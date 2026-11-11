/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonAbelianHSP01.MainResults.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic

/-!
# Elementary abelian two groups and coset intersections

Defines `IsElementaryAbelianTwo` by commutativity and the exponent-two condition, and derives
the self-inverse property. The independent coset result describes the intersection of any left
coset with a subgroup as empty or a coset of the intersection subgroup. See
[IvanyosMagniezSantha2003] for the surrounding analysis.

## Main statements

* `inv_eq_self`: Every element of a group satisfying `IsElementaryAbelianTwo` is its own
  inverse.
* `coset_inter_normal_eq_empty_or_coset`: The intersection of a left coset of `H` with `N` is
  empty or is a left coset of `H ⊓ N` represented by an element of the intersection.

## References

* [Ivanyos et al., 2003][IvanyosMagniezSantha2003]
-/

set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Papers.NonAbelianHSP01.MainResults

/-- The predicate that a group is commutative and every element has square equal to the
identity. -/
structure IsElementaryAbelianTwo (N : Type*) [Group N] : Prop where

  comm : ∀ x y : N, x * y = y * x

  exp_two : ∀ x : N, x ^ 2 = 1

namespace IsElementaryAbelianTwo

variable {N : Type*} [Group N]

/-- Every element of a group satisfying `IsElementaryAbelianTwo` is its own inverse. -/
theorem inv_eq_self (h : IsElementaryAbelianTwo N) (x : N) : x⁻¹ = x := by
  have hx : x * x = 1 := by simpa [pow_two] using h.exp_two x
  exact inv_eq_of_mul_eq_one_right hx

/-- Multiplication commutes in a group satisfying `IsElementaryAbelianTwo`. -/
theorem mul_comm' (h : IsElementaryAbelianTwo N) (x y : N) : x * y = y * x :=
  h.comm x y

end IsElementaryAbelianTwo

section InterCoset

variable {G : Type*} [Group G] {H N : Subgroup G}

/-- The left coset of `H` with representative `z`, as the image of `H` under multiplication by
`z`. -/
def leftCoset (z : G) (H : Subgroup G) : Set G :=
  (fun h : G => z * h) '' (H : Set G)

/-- The intersection of a left coset of `H` with `N` is empty or is a left coset of `H ⊓ N`
represented by an element of the intersection [IvanyosMagniezSantha2003]. -/
theorem coset_inter_normal_eq_empty_or_coset (z : G) :
    leftCoset z H ∩ (N : Set G) = ∅ ∨
      ∃ u : G, u ∈ leftCoset z H ∩ (N : Set G) ∧
        leftCoset z H ∩ (N : Set G) = leftCoset u (H ⊓ N) := by
  by_cases hempty : leftCoset z H ∩ (N : Set G) = ∅
  · exact Or.inl hempty
  · right
    obtain ⟨u, hu⟩ := Set.nonempty_iff_ne_empty.2 hempty
    obtain ⟨hu1, huN⟩ := hu
    obtain ⟨h, hhH, rfl⟩ := hu1
    refine ⟨z * h, ⟨⟨h, hhH, rfl⟩, huN⟩, ?_⟩
    ext x
    constructor
    · rintro ⟨hx1, hxN⟩
      obtain ⟨h', hh'H, rfl⟩ := hx1
      refine ⟨h⁻¹ * h', ⟨?_, ?_⟩, ?_⟩
      · exact H.mul_mem (Subgroup.inv_mem H hhH) hh'H
      · have hmem : (z * h)⁻¹ * (z * h') ∈ N :=
          N.mul_mem (Subgroup.inv_mem N huN) hxN
        simpa using hmem
      · group
    · rintro ⟨k, hk, rfl⟩
      refine ⟨⟨h * k, H.mul_mem hhH hk.1, ?_⟩, ?_⟩
      · group
      · exact N.mul_mem huN hk.2

end InterCoset

end Qatlib.Papers.NonAbelianHSP01.MainResults
