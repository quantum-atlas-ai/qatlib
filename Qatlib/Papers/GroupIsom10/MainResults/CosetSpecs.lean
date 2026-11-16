/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.FiniteGroups.HiddenCosets.Intersection
public import Qatlib.Foundations.FiniteGroups.HiddenCosets.Generators
public import Mathlib.Data.Nat.Log
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section


/-! # Actual coset answers and the literal old length guard

The mathematical input and coset equation are preserved for arbitrary groups,
including the source's abelian specialization. The old per-output existential
constant imposes no short-list bound. No algorithm or runtime is defined here.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical
open Qatlib.Foundations.FiniteGroups.HiddenCosets.Intersection
open Qatlib.Foundations.FiniteGroups.HiddenCosets.Generators

namespace Qatlib.Papers.GroupIsom10.MainResults.CosetSpecs

/-- Actual group elements and generating lists specifying two left cosets. -/
structure CosetInput (G : Type*) [Group G] where
  /-- Generators of the first subgroup. -/
  gens1 : List G
  /-- Generators of the second subgroup. -/
  gens2 : List G
  /-- Representative of the first coset. -/
  x : G
  /-- Representative of the second coset. -/
  y : G

/-- A precise mathematical coset answer, without any claimed resource bound. -/
def CosetValid {G : Type*} [Group G] (inp : CosetInput G)
    (o : Option (G × List G)) : Prop :=
  match o with
  | none => coset inp.x (listClosure inp.gens1) ∩ coset inp.y (listClosure inp.gens2) = ∅
  | some (z, gs) => coset inp.x (listClosure inp.gens1) ∩ coset inp.y (listClosure inp.gens2)
      = coset z (listClosure gs)

/-- The literal old predicate, preserved only to diagnose its per-output constant. -/
def LegacyCosetOk {G : Type*} [Group G] (inp : CosetInput G)
    (o : Option (G × List G)) : Prop :=
  match o with
  | none => coset inp.x (listClosure inp.gens1) ∩ coset inp.y (listClosure inp.gens2) = ∅
  | some (z, gs) => coset inp.x (listClosure inp.gens1) ∩ coset inp.y (listClosure inp.gens2)
      = coset z (listClosure gs) ∧
        ∃ C : ℕ, gs.length ≤ C * (Nat.log2 (Nat.card G + 1) + 1)

/-- The old existential length constant is satisfied by every list and dimension. -/
theorem lengthVacuous {A : Type*} (n : ℕ) (gs : List A) :
    ∃ C : ℕ, gs.length ≤ C * (Nat.log2 (n + 1) + 1) := by
  refine ⟨gs.length, ?_⟩
  calc gs.length = gs.length * 1 := by simp
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.succ_le_succ (Nat.zero_le _))

/-- Removing that universally true guard preserves exactly the old mathematical equation. -/
theorem legacySame {G : Type*} [Group G] (inp : CosetInput G)
    (o : Option (G × List G)) : LegacyCosetOk inp o ↔ CosetValid inp o := by
  cases o with
  | none => rfl
  | some p =>
    rcases p with ⟨z, gs⟩
    change (_ ∧ ∃ C : ℕ, gs.length ≤ C * (Nat.log2 (Nat.card G + 1) + 1)) ↔ _
    constructor
    · exact And.left
    · intro h
      exact ⟨h, lengthVacuous (Nat.card G) gs⟩

end Qatlib.Papers.GroupIsom10.MainResults.CosetSpecs
