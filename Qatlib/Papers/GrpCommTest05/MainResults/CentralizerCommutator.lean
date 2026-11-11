/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Centers, centralizers, and noncommuting group elements

The module characterizes commutative groups by their centers and expresses singleton centralizer
membership as a commutation equation. A noncommutative group has a proper center, and any
noncentral element has a proper centralizer.

These elementary subgroup facts support counting products that fail to commute. See
[MagniezNayak2005].

## Main statements

* `center_eq_top_iff_commutative`: The center of a group is the whole group exactly when every
  pair of elements commutes.
* `centralizer_ne_top_of_not_mem_center`: The centralizer of a noncentral element is a proper
  subgroup.

## References

* [Magniez and Nayak, 2005][MagniezNayak2005]
-/

set_option autoImplicit false

namespace Qatlib.Papers.GrpCommTest05.MainResults

open Subgroup

variable {G : Type*} [Group G]

/-- The center of a group is the whole group exactly when every pair of elements commutes. -/
theorem center_eq_top_iff_commutative :
    Subgroup.center G = ⊤ ↔ ∀ a b : G, a * b = b * a := by
  constructor
  · intro h a b
    have ha : a ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp ha b).symm
  · intro h
    refine top_le_iff.mp ?_
    intro a _
    rw [Subgroup.mem_center_iff]
    intro b
    exact h b a

/-- A group containing a noncommuting pair has a center different from the whole group. See
[MagniezNayak2005]. -/
theorem center_ne_top_of_noncommutative (h : ∃ a b : G, a * b ≠ b * a) :
    Subgroup.center G ≠ ⊤ := by
  intro htop
  obtain ⟨a, b, hab⟩ := h
  exact hab ((center_eq_top_iff_commutative.mp htop) a b)

/-- The centralizer of a noncentral element is a proper subgroup. -/
theorem centralizer_ne_top_of_not_mem_center {g : G} (hg : g ∉ Subgroup.center G) :
    Subgroup.centralizer ({g} : Set G) ≠ ⊤ := by
  intro htop
  apply hg
  rw [Subgroup.mem_center_iff]
  intro b
  have hb : b ∈ Subgroup.centralizer ({g} : Set G) := by rw [htop]; exact Subgroup.mem_top b
  exact (Subgroup.mem_centralizer_iff.mp hb g (Set.mem_singleton g)).symm

/-- An element `h` belongs to the centralizer of `{g}` exactly when `g*h = h*g`. See
[MagniezNayak2005]. -/
theorem mem_centralizer_singleton_iff {g h : G} :
    h ∈ Subgroup.centralizer ({g} : Set G) ↔ g * h = h * g := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro hgh
    exact hgh g (Set.mem_singleton g)
  · intro hgh x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact hgh

end Qatlib.Papers.GrpCommTest05.MainResults
