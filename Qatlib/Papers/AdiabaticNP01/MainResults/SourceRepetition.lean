/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# AdiabaticNP01 — repetition amplification (§10, p. 8)

Source: E. Farhi, J. Goldstone, S. Gutmann, J. Lapan, A. Lundgren, D. Preda,
arXiv:quant-ph/0104129v1 (2001), §10 "Probabilities of success at a proposed
running time", p. 8:

> "If an algorithm (classical or quantum) succeeds with probability at least `p`,
> then running the algorithm `k` times gives a success probability of at least
> `1 − (1 − p)^k`.  For example, if `p = 0.04`, then 200 repetitions of the
> algorithm gives a success probability of better than 0.9997."

This file formalises that arithmetic: the all-fail probability of `k` independent
repetitions is `(1 − p)^k` (`failureProbability`), it can be driven below any
positive target by a repetition count depending only on `p` and the target
(`exists_repetitions_meeting_target`), and the paper's numeric instance
`p = 0.04`, `k = 200` is verified (`two_hundred_repetitions_numeric`).

The repetition count is independent of the number of bits `n`, which is exactly
the role the sentence plays in §10: it converts a fixed worst-case success
probability into any desired overall confidence.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AdiabaticNP01.MainResults

/-- Probability that `k` independent repetitions of a procedure with per-run
success probability `p` all fail: `(1 − p)^k` (§10, p. 8). -/
def failureProbability (p : ℝ) (k : ℕ) : ℝ :=
  (1 - p) ^ k

/-- Success probability of `k` independent repetitions: `1 − (1 − p)^k`
(§10, p. 8). -/
def repetitionSuccessProbability (p : ℝ) (k : ℕ) : ℝ :=
  1 - failureProbability p k

/-- The all-fail probability is antitone in the per-run success probability: a
larger per-run success probability can only lower `(1 − p)^k`.  This is the
monotonicity used to transfer the paper's `p ≥ 1/8` or `p ≥ 0.04` observations to
the repetition bound. -/
theorem failureProbability_anti {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hq1 : q ≤ 1)
    (k : ℕ) : failureProbability q k ≤ failureProbability p k := by
  unfold failureProbability
  exact pow_le_pow_left₀ (by linarith) (by linarith) k

/-- For any per-run success probability `0 < p ≤ 1` and any target `ε > 0`, there
is a number of repetitions `k` (depending only on `p` and `ε`) with all-fail
probability at most `ε`.  This is the "any `n`-independent desired probability of
success can be achieved with a fixed number of repetitions" statement of §10,
p. 8. -/
theorem exists_repetitions_meeting_target {p ε : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hε : 0 < ε) : ∃ k : ℕ, failureProbability p k ≤ ε := by
  have h0 : 0 ≤ 1 - p := by linarith
  have h1 : 1 - p < 1 := by linarith
  have ht : Filter.Tendsto (fun k : ℕ => (1 - p) ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1
  have hev : ∀ᶠ k : ℕ in Filter.atTop, (1 - p) ^ k ≤ ε :=
    (ht.eventually (eventually_lt_nhds hε)).mono fun k hk => le_of_lt hk
  obtain ⟨k, hk⟩ := hev.exists
  exact ⟨k, hk⟩

/-- The same statement phrased for the success probability: `1 − ε` success can be
reached with a fixed number of repetitions. -/
theorem exists_repetitions_success_target {p ε : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hε : 0 < ε) : ∃ k : ℕ, 1 - ε ≤ repetitionSuccessProbability p k := by
  obtain ⟨k, hk⟩ := exists_repetitions_meeting_target hp0 hp1 hε
  exact ⟨k, by unfold repetitionSuccessProbability; linarith⟩

/-- The paper's worked example of §10, p. 8: with per-run success probability
`p = 0.04`, 200 repetitions give success probability better than `0.9997`
(`0.96^200 ≈ 0.000285`). -/
theorem two_hundred_repetitions_numeric :
    (0.9997 : ℝ) < repetitionSuccessProbability 0.04 200 := by
  unfold repetitionSuccessProbability failureProbability
  norm_num

end Qatlib.Papers.AdiabaticNP01.MainResults
