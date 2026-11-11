/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Cyclic

set_option backward.isDefEq.respectTransparency false

/-!
# Solvability of semidirect products

Paper: Morales, arXiv:2608.05321v1.

This module formalizes Proposition 6 (a group is solvable exactly when its
derived series reaches the trivial subgroup) and Lemma 15 (a semidirect
product of an Abelian group with a cyclic group is solvable).
-/

set_option autoImplicit false

namespace Qatlib.Papers.SemidirectHSP26.MainResults.Solvable

open SemidirectProduct

/-- Proposition 6: a group is solvable exactly when some term of its derived
series is the trivial subgroup. -/
theorem isSolvable_iff_derivedSeries_eq_bot (G : Type*) [Group G] :
    Group.IsSolvable G ↔ ∃ n : ℕ, derivedSeries G n = ⊥ :=
  Group.isSolvable_def G

/-- Every cyclic group is commutative. -/
theorem mul_comm_of_isCyclic (G : Type*) [Group G] [IsCyclic G] (a b : G) :
    a * b = b * a := by
  obtain ⟨g, hg⟩ := exists_zpow_surjective G
  obtain ⟨m, rfl⟩ := hg a
  obtain ⟨n, rfl⟩ := hg b
  rw [← zpow_add, add_comm, zpow_add]

/-- Every cyclic group is solvable. -/
theorem isSolvable_of_isCyclic (G : Type*) [Group G] [IsCyclic G] : Group.IsSolvable G :=
  Group.isSolvable_of_comm (mul_comm_of_isCyclic G)

/-- Lemma 15: the semidirect product of an Abelian group with a cyclic group
is solvable. -/
theorem isSolvable_semidirect_of_abelian_cyclic
    {A C : Type*} [Group A] [Group C] [IsCyclic C]
    (φ : C →* MulAut A) (hA : ∀ a b : A, a * b = b * a) :
    Group.IsSolvable (A ⋊[φ] C) := by
  haveI : Group.IsSolvable A := Group.isSolvable_of_comm hA
  haveI : Group.IsSolvable C := isSolvable_of_isCyclic C
  refine Group.isSolvable_of_ker_le_range (SemidirectProduct.inl : A →* A ⋊[φ] C)
    (SemidirectProduct.rightHom : A ⋊[φ] C →* C) ?_
  rw [SemidirectProduct.range_inl_eq_ker_rightHom]

end Qatlib.Papers.SemidirectHSP26.MainResults.Solvable
