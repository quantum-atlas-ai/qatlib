/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.WalkAlgorithms.WalkCorrectedContracts
set_option warningAsError false

namespace Qatlib.Concepts.WalkSearch.WalkAlgorithms

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
