/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GroupIsom10.MainResults.StandardDecomposition.ClassS
public import Mathlib.Data.Fintype.Sets

@[expose] public section


/-! # Pure finite decomposition support

This preserves the genuine closed generating-set argument and adds the
minimum-order condition of fixed arXiv:1001.0608v1 Definition 2.1. It does not
construct the black-box algorithm DECOMPOSE, a short generating list, uniform
polynomial running time, or its probability of a correct nonfailure output.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical
open Qatlib.Papers.GroupIsom10.MainResults.StandardDecomposition

namespace Qatlib.Papers.GroupIsom10.MainResults.DecompSupport

/-- Every class-S group has a finite generating-set version of some decomposition. -/
theorem genDecomp (G : Type*) [Group G] [Fintype G]
    (hS : InClassS G) :
    ∃ (U : Finset G) (ν : G), InD (Subgroup.closure (U : Set G)) ν (orderOf ν) := by
  classical
  obtain ⟨A, y, m, hD⟩ := hS
  let U : Finset G := (Finset.univ : Finset G).filter (fun g => g ∈ A)
  refine ⟨U, y, ?_⟩
  have hcl : Subgroup.closure (U : Set G) = A := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro g hg
      exact (Finset.mem_filter.mp hg).2
    · intro a ha
      exact Subgroup.subset_closure (Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩)
  rw [hcl]
  exact
    { m_pos := by rw [hD.order_y]; exact hD.m_pos
      normal := hD.normal
      comm := hD.comm
      coprime := by simpa [hD.order_y] using hD.coprime
      order_y := rfl
      sup_eq_top := hD.sup_eq_top }

/-- A true minimum-order decomposition exists, as required by Definition 2.1. -/
theorem minDecomp (G : Type*) [Group G] [Fintype G] (hS : InClassS G) :
    ∃ (U : Finset G) (ν : G), InD (Subgroup.closure (U : Set G)) ν (orderOf ν) ∧
      ∀ (B : Subgroup G) (z : G) (m : ℕ), InD B z m → orderOf ν ≤ m := by
  have hex : ∃ m : ℕ, ∃ (A : Subgroup G) (y : G), InD A y m := by
    obtain ⟨A, y, m, hD⟩ := hS
    exact ⟨m, A, y, hD⟩
  obtain ⟨A, y, hD⟩ := Nat.find_spec hex
  let U : Finset G := Finset.univ.filter (fun g => g ∈ A)
  have hcl : Subgroup.closure (U : Set G) = A := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro g hg
      exact (Finset.mem_filter.mp hg).2
    · intro g hg
      exact Subgroup.subset_closure (Finset.mem_filter.mpr ⟨Finset.mem_univ g, hg⟩)
  refine ⟨U, y, ?_, ?_⟩
  · rw [hcl, hD.order_y]
    exact hD
  · intro B z m hm
    rw [hD.order_y]
    exact Nat.find_min' hex ⟨B, z, hm⟩

end Qatlib.Papers.GroupIsom10.MainResults.DecompSupport
