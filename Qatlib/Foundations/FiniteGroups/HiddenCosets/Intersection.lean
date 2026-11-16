/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Tactic.Group

@[expose] public section


/-! # Actual left-coset intersection algebra

The source model is the real set {z | x⁻¹ z ∈ H}, for arbitrary groups.
Changing to a representative in both cosets identifies their intersection
with a coset of H ∩ K. No algorithm, generating-list size, cost or success
probability is encoded by these algebraic identities.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Qatlib.Foundations.FiniteGroups.HiddenCosets.Intersection

variable {G : Type*} [Group G]

/-- Actual left coset, in the literal membership convention used by the source. -/
def coset (x : G) (H : Subgroup G) : Set G := {z | x⁻¹ * z ∈ H}

/-- A member of a genuine coset can be used as its representative. -/
theorem changeBase (H : Subgroup G) (x y : G) (hy : y ∈ coset x H) :
    coset x H = coset y H := by
  change x⁻¹ * y ∈ H at hy
  ext z
  constructor
  · intro hz
    change x⁻¹ * z ∈ H at hz
    change y⁻¹ * z ∈ H
    have heq : y⁻¹ * z = (x⁻¹ * y)⁻¹ * (x⁻¹ * z) := by group
    rw [heq]
    exact H.mul_mem (H.inv_mem hy) hz
  · intro hz
    change y⁻¹ * z ∈ H at hz
    change x⁻¹ * z ∈ H
    have heq : x⁻¹ * z = (x⁻¹ * y) * (y⁻¹ * z) := by group
    rw [heq]
    exact H.mul_mem hy hz

/-- A common representative identifies the intersection with the subgroup infimum. -/
theorem interAt (H K : Subgroup G) (x y z : G)
    (hz : z ∈ coset x H ∩ coset y K) :
    coset x H ∩ coset y K = coset z (H ⊓ K) := by
  rw [changeBase H x z hz.1, changeBase K y z hz.2]
  ext w
  rfl

/-- Two actual left cosets have an empty intersection or one exact intersection coset. -/
theorem interEither (H K : Subgroup G) (x y : G) :
    coset x H ∩ coset y K = ∅ ∨
      ∃ z : G, coset x H ∩ coset y K = coset z (H ⊓ K) := by
  by_cases h : (coset x H ∩ coset y K).Nonempty
  · obtain ⟨z, hz⟩ := h
    exact Or.inr ⟨z, interAt H K x y z hz⟩
  · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp h)

end Qatlib.Foundations.FiniteGroups.HiddenCosets.Intersection
