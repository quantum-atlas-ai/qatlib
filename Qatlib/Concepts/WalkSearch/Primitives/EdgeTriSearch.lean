/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.TriangleContracts
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.WalkSearch.Primitives

open Qatlib.Concepts.WalkSearch.Primitives

theorem lemma1_answer (ets : EdgeTriSearch) {n : ℕ} (G : UGraph n)
    (E : Finset (Fin n × Fin n)) (floor : ℕ) :
    (∀ (ρ : ets.seed) {a b c : Fin n}, ets.run G E floor ρ = some (a, b, c) →
      a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ (a, b) ∈ E ∧ (a, b) ∈ G.edges ∧
        (a, c) ∈ G.edges ∧ (b, c) ∈ G.edges) ∧
    (∀ (ρ : ets.seed),
      (∀ a b c : Fin n, ¬(a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ (a, b) ∈ E ∧
        (a, b) ∈ G.edges ∧ (a, c) ∈ G.edges ∧ (b, c) ∈ G.edges)) →
      ets.run G E floor ρ = none) ∧
    ((∃ a b c : Fin n, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ (a, b) ∈ E ∧
        (a, b) ∈ G.edges ∧ (a, c) ∈ G.edges ∧ (b, c) ∈ G.edges) →
      ((@Finset.univ ets.seed ets.seedFin).filter
          (fun ρ : ets.seed => ets.run G E floor ρ = none)).card *
        (floor + 1) ^ ets.cExp ≤ @Fintype.card ets.seed ets.seedFin) ∧
    (∀ (ρ : ets.seed), ets.cost G E floor ρ ≤
      ets.κ * (Nat.log 2 (E.card + n * (E ∩ G.edges).card + 1) + 2) *
        (Nat.sqrt E.card + Nat.sqrt (n * (E ∩ G.edges).card) + 1)) :=
  by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ρ a b c h
    exact ets.sound G E floor ρ h
  · intro ρ h
    exact ets.reject G E floor ρ h
  · intro h
    exact ets.finds G E floor h
  · intro ρ
    exact ets.charges G E floor ρ

end Qatlib.Concepts.WalkSearch.Primitives
