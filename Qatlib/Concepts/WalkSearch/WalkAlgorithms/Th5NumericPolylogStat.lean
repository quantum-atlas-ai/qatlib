/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.WalkAlgorithms.WalkCorrectedContracts

/-!
# Uniform numerical cost contract for subgraph search

`Th5NumericPolylog` states a uniform cost bound for `hAlg` with fixed pattern size,
collision-solver constant, and upper bound on the checking charge. It requires a least-power
subset size and a positive constant multiplying a cubic logarithmic factor and n^(2 - 2/k).

This isolates a numerical aspect of the quantum search bounds surveyed in [Ambainis2005].

## References

* [Ambainis, 2005][Ambainis2005]
-/

namespace Qatlib.Concepts.WalkSearch.WalkAlgorithms

/-- The proposition that `hAlg` has a uniform cost bound proportional to n^(2 - 2/k) with a
cubic logarithmic factor, for fixed `k ≥ 4`, a positive collision-solver constant, and a
bounded checking charge. The subset size is the least positive integer whose kth power
reaches `n ^ (k - 1)`. -/
def Th5NumericPolylog : Prop :=
  ∀ (k : ℕ), 4 ≤ k → ∀ (kcs : KCollisionSolver), 1 ≤ kcs.κ →
    ∀ (Q : ℕ), ∃ (C : ℝ), 0 < C ∧
      ∀ (n : ℕ), 0 < n → ∀ (H : OGraph k) (hv : Fin k)
        (adj : Fin n → Fin n → Bool) (qH : ℕ), qH ≤ Q →
        ∃ r : ℕ, 1 ≤ r ∧ n ^ (k - 1) ≤ r ^ k ∧ (r - 1) ^ k < n ^ (k - 1) ∧
          ∀ stape : ℕ → kcs.seed,
            ((hAlg adj H hv kcs r qH stape).2 : ℝ) ≤
              C * ((Nat.log 2 n + 2 : ℕ) : ℝ) ^ 3 *
                (n : ℝ) ^ ((2 : ℝ) - 2 / (k : ℝ))

end Qatlib.Concepts.WalkSearch.WalkAlgorithms
