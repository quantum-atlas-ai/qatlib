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

The presentation and four feasibility results below are algebraic existence
results. No execution, oracle-query bound, or polynomial-time algorithm is
constructed. In particular, feasibility is never promoted to `PolySolvable`.
-/

set_option autoImplicit false

namespace Qatlib.Papers.NonAbelianHSP01.MainResults.Claims

/-- **Statement only — not proved in Qatlib.**
Legacy ledger-level projection of Corollary 5. The predicates here do not
encode oracle execution or uniform polynomial complexity. No such algorithm
is asserted by this definition; the proved result is `finite_tasks_feasible`. -/
def corollary_five_statement {G : Type*} [Group G] [Fintype G]
    (B : BlackBoxGroupData G) (Ω : Oracles B) : Prop :=
  PolySolvable B Ω .membershipTest ∧
    PolySolvable B Ω .orderAndPresentation ∧
    PolySolvable B Ω .center ∧ PolySolvable B Ω .sylow

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

/-- Finite-group feasibility of four tasks. This asserts existence of mathematical
objects only; it gives no oracle algorithm or complexity bound. -/
theorem finite_tasks_feasible {G : Type*} [Group G] [Fintype G] (B : BlackBoxGroupData G)
    (Ω : Oracles B) :
    TaskFeasible B Ω .membershipTest ∧
      TaskFeasible B Ω .orderAndPresentation ∧
      TaskFeasible B Ω .center ∧
      TaskFeasible B Ω .sylow := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g
    exact ⟨[(g, 1)], by simp⟩
  · exact exists_presentation G
  · obtain ⟨S, hS⟩ := exists_finset_closure_eq (Subgroup.center G)
    exact ⟨S, hS⟩
  · intro p _
    exact inferInstance

end Qatlib.Papers.NonAbelianHSP01.MainResults.Claims
