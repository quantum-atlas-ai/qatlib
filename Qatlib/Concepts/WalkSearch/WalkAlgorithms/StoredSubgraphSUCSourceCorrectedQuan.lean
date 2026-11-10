/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.WalkAlgorithms.StoredSubgraphSUCSourceCorrectedStat
import Qatlib.Concepts.WalkSearch.WalkAlgorithms.FreshValidationCheckerQuan
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.WalkSearch.WalkAlgorithms

@[simp] theorem mem_storedEdges {n : ℕ} (adj : Fin n → Fin n → Bool)
    (U : Finset (Fin n)) (a b : Fin n) :
    (a, b) ∈ storedEdges adj U ↔ a ∈ U ∧ b ∈ U ∧ adj a b = true := by
  simp [storedEdges, and_assoc]

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

@[simp] theorem mem_storedReplay_queryAnswers {n : ℕ}
    (adj : Fin n → Fin n → Bool) (queries : List (Fin n × Fin n)) (p : Fin n × Fin n) :
    p ∈ storedReplay (storedQueryAnswers adj queries) ↔ p ∈ queries ∧ adj p.1 p.2 = true := by
  classical
  rcases p with ⟨a, b⟩
  simp [storedReplay, storedQueryAnswers]

theorem storedReplay_setup {n : ℕ} (adj : Fin n → Fin n → Bool) (U : Finset (Fin n)) :
    storedReplay (storedQueryAnswers adj (storedSetupQueries U)) = storedEdges adj U := by
  ext p
  rcases p with ⟨a, b⟩
  simp [storedSetupQueries, and_assoc]

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
