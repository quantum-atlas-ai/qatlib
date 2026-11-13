/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.WalkAlgorithms.StoredSubgraphSUCSourceCorrectedStat
import Qatlib.Concepts.WalkSearch.WalkAlgorithms.FreshValidationCheckerQuan

/-!
# Stored-subgraph reconstruction and resource guarantees

This module proves that the stored-edge representation is reconstructed exactly from setup query
answers and updated exactly from incident-edge answers. Symmetric loop-free adjacency ensures
that reversing the update answers supplies the full induced edge set after inserting a vertex.

`storedSubgraphSUCSourceCorrected_answer` combines these identities with edge invariants, setup
and update query counts, and the fresh-checker budget. These are data-structure components for
the setup, update, and checking framework of quantum-walk search [MagniezNayakRolandSantha2011].

## Main statements

* `storedReplay_setup`: exact reconstruction from setup answers.
* `storedReplay_update`: exact reconstruction after a vertex insertion.
* `storedSubgraphSUCSourceCorrected_answer`: the combined stored-subgraph contract.

## References

* [Magniez et al., 2011][MagniezNayakRolandSantha2011]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.WalkSearch.WalkAlgorithms

/-- An ordered pair is a stored edge exactly when both endpoints lie in `U` and the adjacency
query is true. -/
@[simp] theorem mem_storedEdges {n : ℕ} (adj : Fin n → Fin n → Bool)
    (U : Finset (Fin n)) (a b : Fin n) :
    (a, b) ∈ storedEdges adj U ↔ a ∈ U ∧ b ∈ U ∧ adj a b = true := by
  simp [storedEdges, and_assoc]

/-- For symmetric loop-free adjacency, adding the edges incident to `v` reconstructs the stored
induced edge set on `insert v U`. -/
theorem storedInsert_eq {n : ℕ} (adj : Fin n → Fin n → Bool)
    (hs : ∀ a b, adj a b = adj b a) (hl : ∀ a, adj a a = false)
    (U : Finset (Fin n)) (v : Fin n) :
    storedInsert adj U v = storedEdges adj (insert v U) := by
  classical
  ext p
  rcases p with ⟨a, b⟩
  by_cases ha : a = v <;> by_cases hb : b = v
  · subst a; subst b
    simp [storedInsert, hl]
  · subst a
    simp [storedInsert, hb, Ne.symm hb, hs]
  · subst b
    simp only [storedInsert, Finset.mem_union, mem_storedEdges, Finset.mem_image,
      Finset.mem_filter, Prod.mk.injEq, Finset.mem_insert]
    simp [ha, Ne.symm ha]
    intro hA _ hE
    exact ⟨hA, hE⟩
  · simp [storedInsert, ha, hb, Ne.symm ha, Ne.symm hb]

/-- Replaying adjacency answers retains exactly the queried pairs whose adjacency value is true. -/
@[simp] theorem mem_storedReplay_queryAnswers {n : ℕ}
    (adj : Fin n → Fin n → Bool) (queries : List (Fin n × Fin n)) (p : Fin n × Fin n) :
    p ∈ storedReplay (storedQueryAnswers adj queries) ↔ p ∈ queries ∧ adj p.1 p.2 = true := by
  classical
  rcases p with ⟨a, b⟩
  simp [storedReplay, storedQueryAnswers]

/-- Replaying all setup query answers reconstructs the stored edge set on `U`. -/
theorem storedReplay_setup {n : ℕ} (adj : Fin n → Fin n → Bool) (U : Finset (Fin n)) :
    storedReplay (storedQueryAnswers adj (storedSetupQueries U)) = storedEdges adj U := by
  ext p
  rcases p with ⟨a, b⟩
  simp [storedSetupQueries, and_assoc]

/-- For symmetric loop-free adjacency, inserting the replayed update answers and their reversals
reconstructs the stored edge set on `insert v U`. -/
theorem storedReplay_update {n : ℕ} (adj : Fin n → Fin n → Bool)
    (hs : ∀ a b, adj a b = adj b a) (hl : ∀ a, adj a a = false)
    (U : Finset (Fin n)) (v : Fin n) :
    storedReplayInsert (storedEdges adj U)
      (storedQueryAnswers adj (storedUpdateQueries U v)) = storedEdges adj (insert v U) := by
  have heq : storedReplay (storedQueryAnswers adj (storedUpdateQueries U v)) =
      (U.filter (fun a => adj a v = true)).image (fun a => (a, v)) := by
    ext p
    rcases p with ⟨a, b⟩
    simp only [mem_storedReplay_queryAnswers, storedUpdateQueries, List.mem_map,
      Finset.mem_toList, Finset.mem_image, Finset.mem_filter, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨x, hx, hxa, hvb⟩, he⟩
      subst x; subst b
      exact ⟨a, ⟨hx, he⟩, rfl, rfl⟩
    · rintro ⟨x, ⟨hx, he⟩, hxa, hvb⟩
      subst x; subst b
      exact ⟨⟨a, hx, rfl, rfl⟩, he⟩
  rw [storedReplayInsert, heq, Finset.image_image]
  exact storedInsert_eq adj hs hl U v

/-- Establish the stored-subgraph contract, including edge invariants, setup and update query
counts, exact replay reconstruction, and the fresh-checker cost bound. -/
theorem storedSubgraphSUCSourceCorrected_answer : StoredSubgraphSUCSourceCorrected := by
  intro n adj hs hl U
  refine ⟨mem_storedEdges adj U, ?_, ?_, ?_, ?_, ?_, storedInsert_eq adj hs hl U,
    storedReplay_setup adj U, storedReplay_update adj hs hl U, ?_⟩
  · intro a b hab
    rcases (mem_storedEdges adj U a b).mp hab with ⟨ha, hb, he⟩
    exact (mem_storedEdges adj U b a).mpr ⟨hb, ha, (hs b a).trans he⟩
  · intro a
    simp [hl]
  · simp [storedSetupQueries]
  · simp [storedSetupQueries]
  · intro v
    simp [storedUpdateQueries]
  · intro kcs ncs r' c₀ hk hn stape ntape
    exact (freshValidationChecker_answer n adj U kcs ncs r' c₀ hk hn).2.2 stape ntape

end Qatlib.Concepts.WalkSearch.WalkAlgorithms
