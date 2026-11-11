/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.WalkAlgorithms.StoredSubgraphVocabulary

/-!
# Stored-subgraph setup, update, and checking contract

`StoredSubgraphSUCSourceCorrected` records the induced-edge representation for symmetric
loop-free adjacency. It requires edge membership, symmetry, absence of loops, a setup query list
of size `U.card^2`, and an update query list of size `U.card`, together with exact insertion and
replay identities.

The contract also includes the fresh-checker cost bound when the solver constants are at least
one. It supplies a concrete data-structure specification in the setup, update, and checking
perspective on quantum-walk search [MagniezNayakRolandSantha2011].

## Main statements

* `StoredSubgraphSUCSourceCorrected`: representation, query-count, replay, and checker-cost
  requirements.

## References

* [Magniez et al., 2011][MagniezNayakRolandSantha2011]
-/

set_option warningAsError false

namespace Qatlib.Concepts.WalkSearch.WalkAlgorithms

/-- The stored-subgraph contract for symmetric loop-free adjacency, specifying induced-edge
invariants, exact setup and update query counts, replay reconstruction, and the
fresh-checker cost bound under the solver-constant hypotheses. -/
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
