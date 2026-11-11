/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit

/-!
# The rejection-budget contract

`RejectionBudget` states an abstract implication from a uniform rejection-tail bound to a lower
bound on a power of the success probability. The hypothesis controls every natural round index,
including zero. These estimates concern rejection rewinding in quantum Metropolis sampling
[TemmeEtAl2011].

## Main statements

* `RejectionBudget`: The proposition that `0 ≤ pfail n ≤ 1 / (2 * (n + 1))` at every round
  implies `(1 - pfail n) ^ m ≥ c` whenever the stated round budget holds.

## References

* [Temme et al., 2011][TemmeEtAl2011]
-/

namespace Qatlib.Concepts.QuantumGibbs.RejectionRewind

/-- The proposition that `0 ≤ pfail n ≤ 1 / (2 * (n + 1))` at every round implies `(1 - pfail n)
^ m ≥ c` whenever the stated round budget holds. -/
def RejectionBudget : Prop :=
  ∀ pfail : ℕ → ℝ,
    (∀ n, 0 ≤ pfail n ∧ pfail n ≤ 1 / (2 * (n + 1))) →
    ∀ (m n : ℕ) (c : ℝ), 0 ≤ c → c < 1 → 0 < m →
      (n + 1) * (2 * (1 - c)) ≥ m → (1 - pfail n) ^ m ≥ c

end Qatlib.Concepts.QuantumGibbs.RejectionRewind
