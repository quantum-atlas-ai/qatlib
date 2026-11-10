/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonAbelianHSP01.MainResults.Defs
import Qatlib.Papers.NonAbelianHSP01.MainResults.Reductions
import Mathlib.GroupTheory.PresentedGroup
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Papers.NonAbelianHSP01.MainResults.Claims

theorem polySolvable_of_feasible {G : Type*} [Group G] {B : BlackBoxGroupData G}
    {Ω : Oracles B} {t : Task} (h : TaskFeasible B Ω t) : PolySolvable B Ω t := by
  refine ⟨⟨t, CostLedger.zero, ?_, h⟩, rfl⟩
  refine ⟨1, 0, ?_⟩
  simp [CostLedger.total, CostLedger.zero]

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
