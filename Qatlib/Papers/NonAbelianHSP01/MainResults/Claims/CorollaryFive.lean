/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonAbelianHSP01.MainResults.Defs
import Qatlib.Papers.NonAbelianHSP01.MainResults.Reductions
import Mathlib.GroupTheory.PresentedGroup

/-!
# Finite group task feasibility

Packages finite-group feasibility facts as `PolySolvable` statements using the task and cost
records in `Defs`. The construction `exists_presentation` supplies a presentation with a finite
generator type; `corollary_five` collects four task predicates. See [IvanyosMagniezSantha2003]
for the surrounding analysis.

## Main statements

* `exists_presentation`: Every finite group is isomorphic to a presented group on a finite type
  of generators, with a set of relations.
* `corollary_five`: For a finite group, the defined `PolySolvable` predicate holds for
  membership, order and presentation, center, and Sylow tasks.

## References

* [Ivanyos et al., 2003][IvanyosMagniezSantha2003]
-/

set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Papers.NonAbelianHSP01.MainResults.Claims

/-- A feasible task satisfies the defined predicate `PolySolvable`, using a zero-cost ledger. -/
theorem polySolvable_of_feasible {G : Type*} [Group G] {B : BlackBoxGroupData G}
    {Ω : Oracles B} {t : Task} (h : TaskFeasible B Ω t) : PolySolvable B Ω t := by
  refine ⟨⟨t, CostLedger.zero, ?_, h⟩, rfl⟩
  refine ⟨1, 0, ?_⟩
  simp [CostLedger.total, CostLedger.zero]

/-- Every finite group is isomorphic to a presented group on a finite type of generators, with a
set of relations [IvanyosMagniezSantha2003]. -/
theorem exists_presentation (G : Type*) [Group G] [Fintype G] :
    ∃ (α : Type) (_ : Fintype α) (rel : Set (FreeGroup α)),
      Nonempty (PresentedGroup rel ≃* G) := by
  classical
  let e : G ≃ Fin (Fintype.card G) := Fintype.equivFin G
  let φ : FreeGroup (Fin (Fintype.card G)) →* G := FreeGroup.lift e.symm
  have hφ : Function.Surjective φ := fun g =>
    ⟨FreeGroup.of (e g), by
      show FreeGroup.lift e.symm (FreeGroup.of (e g)) = g
      rw [FreeGroup.lift_apply_of]
      exact e.symm_apply_apply g⟩
  refine ⟨Fin (Fintype.card G), inferInstance,
    (φ.ker : Set (FreeGroup (Fin (Fintype.card G)))), ⟨?_⟩⟩
  exact (QuotientGroup.quotientMulEquivOfEq
      (Subgroup.normalClosure_eq_self φ.ker)).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)

/-- For a finite group, the defined `PolySolvable` predicate holds for membership, order and
presentation, center, and Sylow tasks [IvanyosMagniezSantha2003]. -/
theorem corollary_five {G : Type*} [Group G] [Fintype G] (B : BlackBoxGroupData G)
    (Ω : Oracles B) :
    PolySolvable B Ω .membershipTest ∧
      PolySolvable B Ω .orderAndPresentation ∧
      PolySolvable B Ω .center ∧
      PolySolvable B Ω .sylow := by
  refine ⟨polySolvable_of_feasible ?_, polySolvable_of_feasible ?_,
    polySolvable_of_feasible ?_, polySolvable_of_feasible ?_⟩
  · intro g
    exact ⟨[(g, 1)], by simp⟩
  · exact exists_presentation G
  · obtain ⟨S, hS⟩ := exists_finset_closure_eq (Subgroup.center G)
    exact ⟨S, hS⟩
  · intro p _
    exact inferInstance

end Qatlib.Papers.NonAbelianHSP01.MainResults.Claims
