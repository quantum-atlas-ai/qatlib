/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer

set_option autoImplicit false

namespace Qatlib.Papers.GrpCommTest05.MainResults

open Subgroup

variable {G : Type*} [Group G]

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

theorem center_ne_top_of_noncommutative (h : ∃ a b : G, a * b ≠ b * a) :
    Subgroup.center G ≠ ⊤ := by
  intro htop
  obtain ⟨a, b, hab⟩ := h
  exact hab ((center_eq_top_iff_commutative.mp htop) a b)

theorem centralizer_ne_top_of_not_mem_center {g : G} (hg : g ∉ Subgroup.center G) :
    Subgroup.centralizer ({g} : Set G) ≠ ⊤ := by
  intro htop
  apply hg
  rw [Subgroup.mem_center_iff]
  intro b
  have hb : b ∈ Subgroup.centralizer ({g} : Set G) := by rw [htop]; exact Subgroup.mem_top b
  exact (Subgroup.mem_centralizer_iff.mp hb g (Set.mem_singleton g)).symm

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
