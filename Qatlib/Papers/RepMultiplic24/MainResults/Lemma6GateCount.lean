/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RepMultiplic24.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# RepMultiplic24.MainResults.Lemma6GateCount

Paper: *Quantum Algorithms for Representation-Theoretic Multiplicities*,
fixed arXiv:2407.17649 (2024), Claim `c009` = Lemma 6 (main text p. 8).

Lemma 6: the Kronecker-coefficient algorithm requires `O(n^4)` elementary gates
per shot.

Proof route (paper): a shot of the Kronecker algorithm applies two `Sₙ`-QFTs
(`G`-QFT with `G = Sₙ`), prepares the required state, and applies the controlled
regular action. The paper cites [23] for the `Sₙ`-QFT being implementable with
`O(n^4)` gates; the controlled regular action costs `O(n^3)`; preparation is
absorbed in the same `O(n^4)` budget. Hence the per-shot total is `O(n^4)`.

Formalisation: `KroneckerShot n` bundles the three component sizes together
with the paper's cited bounds (`qft ≤ n^4`, `prepare ≤ n^4`,
`controlled ≤ n^3`). The theorem then proves the *accounting* claim: the sum is
at most `3 n^4`. The cited component bounds are the paper's own proof steps
(external QFT compilation), not additional assumptions about the algorithm.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Qatlib.Papers.RepMultiplic24.MainResults

/-- One shot of the Kronecker-coefficient algorithm, decomposed into the two
`Sₙ`-QFTs, the state preparation, and the controlled regular action, with the
paper's cited component gate counts (`n^4` for the `Sₙ`-QFT [23], `n^3` for the
controlled action). -/
structure KroneckerShot (n : ℕ) where
  /-- Gates for the two `Sₙ`-QFTs. -/
  qftGates : ℕ
  /-- Gates for state preparation. -/
  prepareGates : ℕ
  /-- Gates for the controlled regular action. -/
  controlledGates : ℕ
  qft_le : qftGates ≤ n ^ 4
  prepare_le : prepareGates ≤ n ^ 4
  controlled_le : controlledGates ≤ n ^ 3

/-- Per-shot gate count. -/
def KroneckerShot.perShot {n : ℕ} (s : KroneckerShot n) : ℕ :=
  s.qftGates + s.prepareGates + s.controlledGates

/-- **Lemma 6 (c009).** For `n ≥ 1`, one shot of the Kronecker algorithm uses at
most `3 n^4` elementary gates, i.e. `O(n^4)`.

Paper: fixed arXiv:2407.17649, Lemma 6 ("`O(n^4)` elementary gates per shot"),
using the `Sₙ`-QFT bound of [23] and the `O(n^3)` controlled action. -/
theorem lemma6_per_shot_gates (n : ℕ) (hn : 1 ≤ n) (s : KroneckerShot n) :
    s.perShot ≤ 3 * n ^ 4 := by
  have h1 := s.qft_le
  have h2 := s.prepare_le
  have h3 := s.controlled_le
  have h34 : n ^ 3 ≤ n ^ 4 :=
    Nat.pow_le_pow_right (by omega) (by norm_num : 3 ≤ 4)
  unfold KroneckerShot.perShot
  have hsum : s.qftGates + s.prepareGates + s.controlledGates ≤ n ^ 4 + n ^ 4 + n ^ 3 :=
    Nat.add_le_add (Nat.add_le_add h1 h2) h3
  have hgoal : n ^ 4 + n ^ 4 + n ^ 3 ≤ 3 * n ^ 4 := by omega
  exact le_trans hsum hgoal

/-- **Lemma 6 (c009), big-O form.** There is a constant `c` (here `3`) such that
every shot of the Kronecker algorithm uses at most `c n^4` gates.

Paper: fixed arXiv:2407.17649, Lemma 6. -/
theorem lemma6_gate_bound (n : ℕ) (hn : 1 ≤ n) :
    ∃ c : ℕ, 0 < c ∧ ∀ s : KroneckerShot n, s.perShot ≤ c * n ^ 4 :=
  ⟨3, by norm_num, fun s => lemma6_per_shot_gates n hn s⟩

end Qatlib.Papers.RepMultiplic24.MainResults
