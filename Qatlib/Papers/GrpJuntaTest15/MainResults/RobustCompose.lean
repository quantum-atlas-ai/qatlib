/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GrpJuntaTest15.MainResults.SourceModel

@[expose] public section

/-!
# Composition with irrelevant variables

Definition 2.10 of arXiv:1507.03126v1 defines a composition by matching
only the relevant coordinates of a witness. Proposition 2.11 explains
why the diagonal support of an adversary SDP solution provides a
consistent relevance relation.
-/

set_option autoImplicit false

open Matrix
open scoped ComplexOrder
open Qatlib.Papers.GrpJuntaTest15.MainResults.SourceModel

namespace Qatlib.Papers.GrpJuntaTest15.MainResults

variable {n : ℕ} {m : Fin n → ℕ} {F : PartialBoolFun (Fin n → Bool)}
  {rel : (Fin n → Bool) → Fin n → Prop} {G : ∀ j, PartialBoolFun (Fin (m j) → Bool)}

/-- Two witnesses matching all relevant coordinates give the same outer
Boolean value under the consistency condition of Definition 2.8. -/
theorem robustCompose_val_wellDefined (hcons : IrrelevantConsistent F rel)
    {x : ∀ j, Fin (m j) → Bool} (h₁ h₂ : (robustCompose m F rel G).dom x) :
    F.val (Classical.choose h₁) = F.val (Classical.choose h₂) := by
  have hw₁ := Classical.choose_spec h₁
  have hw₂ := Classical.choose_spec h₂
  by_contra hne
  obtain ⟨j, hj₁, hj₂, hjne⟩ := hcons _ _ hw₁.1 hw₂.1 hne
  exact hjne ((hw₁.2 j hj₁).2.symm.trans (hw₂.2 j hj₂).2)

/-- The composition evaluates to the outer value of any matching witness
in Definition 2.10, including the witnesses not selected by choice. -/
theorem robustCompose_val_eq (hcons : IrrelevantConsistent F rel)
    {x : ∀ j, Fin (m j) → Bool} {z : Fin n → Bool} (hz : F.dom z)
    (hmatch : ∀ j, rel z j → (G j).dom (x j) ∧ (G j).val (x j) = z j) :
    (robustCompose m F rel G).val x = F.val z := by
  have hdom : ∃ z, F.dom z ∧ ∀ j, rel z j → (G j).dom (x j) ∧ (G j).val (x j) = z j :=
    ⟨z, hz, hmatch⟩
  simp only [robustCompose, dite_eq_left hdom]
  have hw := Classical.choose_spec hdom
  by_contra hne
  obtain ⟨j, hjw, hjz, hjne⟩ := hcons _ _ hw.1 hz hne
  exact hjne ((hw.2 j hjw).2.symm.trans (hmatch j hjz).2)

/-- A zero diagonal entry of a positive semidefinite matrix forces its
column to vanish. -/
private theorem psd_entry_zero_of_diag_zero {X : Type} [Fintype X] [DecidableEq X]
    {A : Matrix X X ℂ} (hA : A.PosSemidef) {x y : X} (hy : A y y = 0) : A x y = 0 := by
  have hstar : star (Pi.single y (1 : ℂ) : X → ℂ) = Pi.single y 1 := by rw [← Pi.single_star, star_one]
  have hquad : star (Pi.single y (1 : ℂ)) ⬝ᵥ A *ᵥ Pi.single y 1 = 0 := by
    rw [hstar, Matrix.mulVec_single_one, single_dotProduct, one_mul]
    exact hy
  have hcol := hA.dotProduct_mulVec_zero_iff.mp hquad
  rw [Matrix.mulVec_single_one] at hcol
  exact congrFun hcol x

/-- The nonzero diagonals of a feasible adversary SDP family satisfy the
relevance consistency condition used in Proposition 2.11. -/
theorem advFeasible_diagonalRelevant_consistent
    (M : Fin n → Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
    (hM : AdvFeasible (fun x j => x j) F M) :
    IrrelevantConsistent F (diagonalRelevant M) := by
  classical
  intro x y hx hy hne
  have hsum := hM.2 x y hx hy hne
  have hsome : ∃ j ∈ Finset.univ.filter (fun j => x j ≠ y j), M j x y ≠ 0 := by
    by_contra! hzero
    exact zero_ne_one ((Finset.sum_eq_zero hzero).symm.trans hsum)
  obtain ⟨j, hj, hxy⟩ := hsome
  refine ⟨j, ?_, ?_, (Finset.mem_filter.mp hj).2⟩
  · intro hxx
    have hyx := psd_entry_zero_of_diag_zero (hM.1 j) (x := y) hxx
    apply hxy
    simpa [hyx] using ((hM.1 j).isHermitian.apply x y).symm
  · exact fun hyy => hxy (psd_entry_zero_of_diag_zero (hM.1 j) hyy)

end Qatlib.Papers.GrpJuntaTest15.MainResults
