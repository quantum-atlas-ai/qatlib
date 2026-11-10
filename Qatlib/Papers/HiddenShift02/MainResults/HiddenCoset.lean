/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace Qatlib.Papers.HiddenShift02.MainResults.HiddenCoset

variable {G : Type*} [AddCommGroup G] {β : Type*}

def solutionSet (f g : G → β) : Set G := {t | ∀ x, f x = g (x + t)}

def cosetStabilizer (g : G → β) : AddSubgroup G where
  carrier := {t | ∀ x, g (x + t) = g x}
  zero_mem' := by
    intro x
    rw [add_zero]
  add_mem' := by
    intro a b ha hb x
    rw [← add_assoc, hb, ha]
  neg_mem' := by
    intro a ha x
    have h := ha (x + -a)
    simpa [add_assoc, add_comm, add_left_comm] using h.symm

@[simp] theorem mem_cosetStabilizer {g : G → β} {t : G} :
    t ∈ cosetStabilizer g ↔ ∀ x, g (x + t) = g x := Iff.rfl

theorem g_constant_on_coset (g : G → β) {h : G} (hh : h ∈ cosetStabilizer g) :
    ∀ x, g (x + h) = g x :=
  hh

theorem solution_sub_mem_stabilizer (f g : G → β) {s : G}
    (hs : ∀ x, f x = g (x + s)) {t : G} (ht : t ∈ solutionSet f g) :
    t - s ∈ cosetStabilizer g := by
  intro x

  have h := (hs (x - s)).symm.trans (ht (x - s))
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h.symm

theorem add_stabilizer_mem_solution (f g : G → β) {s : G}
    (hs : ∀ x, f x = g (x + s)) {h : G} (hh : h ∈ cosetStabilizer g) :
    s + h ∈ solutionSet f g := by
  intro x
  rw [← add_assoc]
  exact (hs x).trans (hh (x + s)).symm

theorem source_lemma3 (f g : G → β) {s : G} (hs : ∀ x, f x = g (x + s)) :
    solutionSet f g = {t | ∃ h ∈ cosetStabilizer g, t = s + h} := by
  ext t
  constructor
  · intro ht
    refine ⟨t - s, solution_sub_mem_stabilizer f g hs ht, ?_⟩
    abel
  · rintro ⟨h, hh, rfl⟩
    exact add_stabilizer_mem_solution f g hs hh

theorem cosetStabilizer_isLargest (g : G → β) (K : AddSubgroup G)
    (hK : ∀ k ∈ K, ∀ x, g (x + k) = g x) : K ≤ cosetStabilizer g := by
  intro k hk
  exact hK k hk

theorem source_solution_nonempty (f g : G → β) {s : G}
    (hs : ∀ x, f x = g (x + s)) : (solutionSet f g).Nonempty :=
  ⟨s, hs⟩

theorem source_unique_shift_of_injective (f g : G → β)
    (hinj : Function.Injective g) {s t : G}
    (hs : ∀ x, f x = g (x + s)) (ht : ∀ x, f x = g (x + t)) : t = s := by
  have hEq : ∀ x, g (x + s) = g (x + t) := fun x => (hs x).symm.trans (ht x)
  have h0 := hEq (-s)
  rw [neg_add_cancel] at h0
  have h1 : -s + t = 0 := (hinj h0).symm
  exact eq_of_sub_eq_zero (by simpa [sub_eq_add_neg, add_comm] using h1)

end Qatlib.Papers.HiddenShift02.MainResults.HiddenCoset
