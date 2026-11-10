/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.WalkAlgorithms.StoredSubgraphVocabulary
set_option warningAsError false

namespace Qatlib.Concepts.WalkSearch.WalkAlgorithms

def StoredSubgraphSUCSourceCorrected : Prop :=
  ∀ (n : ℕ) (adj : Fin n → Fin n → Bool),
    (∀ a b, adj a b = adj b a) → (∀ a, adj a a = false) →
    ∀ (U : Finset (Fin n)),
      (∀ a b, (a, b) ∈ storedEdges adj U ↔ a ∈ U ∧ b ∈ U ∧ adj a b = true) ∧
      (∀ a b, (a, b) ∈ storedEdges adj U → (b, a) ∈ storedEdges adj U) ∧
      (∀ a, (a, a) ∉ storedEdges adj U) ∧
      (storedSetupQueries U).toFinset = U.product U ∧
      (storedSetupQueries U).length = U.card * U.card ∧
      (∀ v, (storedUpdateQueries U v).length = U.card) ∧
      (∀ v, storedInsert adj U v = storedEdges adj (insert v U)) ∧
      storedReplay (storedQueryAnswers adj (storedSetupQueries U)) = storedEdges adj U ∧
      (∀ v, storedReplayInsert (storedEdges adj U)
        (storedQueryAnswers adj (storedUpdateQueries U v)) = storedEdges adj (insert v U)) ∧
      ∀ (kcs : KCollisionSolver) (ncs : NoisySearch) (r' c₀ : ℕ),
        1 ≤ kcs.κ → 1 ≤ ncs.κ →
        ∀ (stape : ℕ → kcs.seed) (ntape : ncs.seed),
          (triCheckFresh adj U kcs ncs r' c₀ stape ntape).2 ≤
            2 * cCOf kcs ncs n U.card r' c₀

end Qatlib.Concepts.WalkSearch.WalkAlgorithms
