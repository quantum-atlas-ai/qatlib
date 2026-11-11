/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

/-!
# Lifting subgroup generators through a quotient

For a normal subgroup `K`, describes fibers of the quotient projection inside a subgroup `L` as
cosets of `L ⊓ K`. The theorem `closure_union_lifts` reconstructs generators for `L` from lifts
of generators of its quotient image and generators of its intersection with the kernel. See
[MooreEtAl2002].

## Main statements

* `fiber_mem_coset`: the quotient fiber inside `L` is a coset of `L ⊓ K`.
* `closure_union_lifts`: quotient-image lifts and kernel-intersection generators generate `L`.

## References

* [Moore et al., 2002][MooreEtAl2002]
-/

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.AffineHSP02.SmallExtension

variable {G : Type*} [Group G]

/-- The canonical group homomorphism from `G` to the quotient by the normal subgroup `K`. -/
abbrev proj (K : Subgroup G) [K.Normal] : G →* G ⧸ K := QuotientGroup.mk' K

/-- For `x ∈ L`, an element `y` belongs to `L` and has the same quotient image as `x` exactly
when `y = x * k` for some `k ∈ L ⊓ K`. -/
theorem fiber_mem_coset (K : Subgroup G) [K.Normal] (L : Subgroup G) {x : G}
    (hx : x ∈ L) (y : G) :
    y ∈ L ∧ proj K y = proj K x ↔ ∃ k ∈ L ⊓ K, y = x * k := by
  constructor
  · rintro ⟨hy, hyx⟩
    have hkL : x⁻¹ * y ∈ L := L.mul_mem (L.inv_mem hx) hy
    have hkK : x⁻¹ * y ∈ K := by
      have h1 : proj K (x⁻¹ * y) = 1 := by
        rw [map_mul, map_inv, hyx, inv_mul_cancel]
      have hker : x⁻¹ * y ∈ (proj K).ker := MonoidHom.mem_ker.mpr h1
      simpa [proj, QuotientGroup.ker_mk'] using hker
    refine ⟨x⁻¹ * y, Subgroup.mem_inf.mpr ⟨hkL, hkK⟩, ?_⟩
    group
  · rintro ⟨k, hk, rfl⟩
    have hkL : k ∈ L := (Subgroup.mem_inf.mp hk).1
    refine ⟨L.mul_mem hx hkL, ?_⟩
    rw [map_mul]
    have hkK : k ∈ K := (Subgroup.mem_inf.mp hk).2
    have hk1 : proj K k = 1 := by
      have hker : k ∈ (proj K).ker := by simpa [proj, QuotientGroup.ker_mk'] using hkK
      exact MonoidHom.mem_ker.mp hker
    rw [hk1, mul_one]

/-- If `x ∈ L` and `x` and `y` have the same quotient image, membership of `y` in `L` is
equivalent to `y = x * k` for some `k ∈ L ⊓ K`. -/
theorem mem_iff_mul_mem_inter (K : Subgroup G) [K.Normal] (L : Subgroup G) {x : G}
    (hx : x ∈ L) (y : G) (hyx : proj K y = proj K x) :
    y ∈ L ↔ ∃ k ∈ L ⊓ K, y = x * k := by
  constructor
  · intro hy
    exact (fiber_mem_coset K L hx y).mp ⟨hy, hyx⟩
  · intro h
    exact ((fiber_mem_coset K L hx y).mpr h).1

/-- If the images of `S ⊆ L` generate the quotient image of `L` and `T ⊆ L ⊓ K` generates `L ⊓
K`, then `S ∪ T` generates `L`. -/
theorem closure_union_lifts (K : Subgroup G) [K.Normal] (L : Subgroup G)
    (S T : Set G) (hS : S ⊆ L) (hT : T ⊆ L ⊓ K)
    (himg : L.map (proj K) = Subgroup.closure (proj K '' S))
    (hker : L ⊓ K = Subgroup.closure T) :
    L = Subgroup.closure (S ∪ T) := by
  apply le_antisymm
  · intro x hx

    have hxmap : proj K x ∈ Subgroup.closure (proj K '' S) := by
      rw [← himg]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have hxmap' : proj K x ∈ Subgroup.map (proj K) (Subgroup.closure S) := by
      rw [MonoidHom.map_closure]
      exact hxmap
    obtain ⟨y, hyS, hyx⟩ := Subgroup.mem_map.mp hxmap'
    have hyL : y ∈ L := (Subgroup.closure_le L).mpr hS hyS

    have hkL : x⁻¹ * y ∈ L := L.mul_mem (L.inv_mem hx) hyL
    have hkK : x⁻¹ * y ∈ K := by
      have h1 : proj K (x⁻¹ * y) = 1 := by
        rw [map_mul, map_inv, hyx, inv_mul_cancel]
      have hker : x⁻¹ * y ∈ (proj K).ker := MonoidHom.mem_ker.mpr h1
      simpa [proj, QuotientGroup.ker_mk'] using hker
    have hkT : x⁻¹ * y ∈ Subgroup.closure T := by
      rw [← hker]
      exact Subgroup.mem_inf.mpr ⟨hkL, hkK⟩

    have hyCl : y ∈ Subgroup.closure (S ∪ T) :=
      Subgroup.closure_mono (Set.subset_union_left) hyS
    have hkCl : x⁻¹ * y ∈ Subgroup.closure (S ∪ T) :=
      Subgroup.closure_mono (Set.subset_union_right) hkT
    have hxeq : x = y * (x⁻¹ * y)⁻¹ := by group
    rw [hxeq]
    exact (Subgroup.closure (S ∪ T)).mul_mem hyCl ((Subgroup.closure (S ∪ T)).inv_mem hkCl)
  · exact (Subgroup.closure_le L).mpr (by
      intro z hz
      rcases hz with hz | hz
      · exact hS hz
      · exact (Subgroup.mem_inf.mp (hT hz)).1)

end Qatlib.Papers.AffineHSP02.SmallExtension
