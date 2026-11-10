/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit

namespace Qatlib.Concepts.QuantumGibbs.RejectionRewind

def RejectionBudget : Prop :=
  ∀ pfail : ℕ → ℝ,
    (∀ n, 0 ≤ pfail n ∧ pfail n ≤ 1 / (2 * (n + 1))) →
    ∀ (m n : ℕ) (c : ℝ), 0 ≤ c → c < 1 → 0 < m →
      (n + 1) * (2 * (1 - c)) ≥ m → (1 - pfail n) ^ m ≥ c

end Qatlib.Concepts.QuantumGibbs.RejectionRewind
