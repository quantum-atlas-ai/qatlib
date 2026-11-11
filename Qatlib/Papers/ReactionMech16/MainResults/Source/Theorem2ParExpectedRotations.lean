/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 2: expected number of rotations before a PAR failure

Source: arXiv:1605.03590v2, Appendix E, Theorem 2 (p.18, Eq. (E4)).
A cached PAR rotation fails when all `n` pre-computed correction circuits fail;
each attempt succeeds independently with probability `1/2`, so a failure has
probability `p = 2^{-n}`.  With `M` cached rotations the number of attempts before
a failure is the geometric variable `K` truncated at `M`, and the paper computes

`E[min(K, M)] = ∑_{k=1}^{M} k p (1-p)^{k-1} + M (1-p)^M
              = 2^n (1 - (1 - 2^{-n})^M)`.

We prove the finite truncated-geometric expectation identity for general `p ≠ 0`
and then specialize to `p = 2^{-n}`.  This is exactly Eq. (E4).
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.ReactionMech16.MainResults.Source

/-- Truncated geometric expectation (arXiv:1605.03590v2, Eq. (E4), general `p`):
`∑_{k=0}^{M-1} (k+1) p (1-p)^k + M (1-p)^M = (1 - (1-p)^M) / p`.
The summand is the probability that a failure first appears after exactly `k+1`
attempts, with the final `M (1-p)^M` term accounting for the `M` cached rotations. -/
theorem truncated_geometric_expectation (p : ℝ) (hp : p ≠ 0) (M : ℕ) :
    (∑ k ∈ Finset.range M, ((k : ℝ) + 1) * p * (1 - p) ^ k) +
        (M : ℝ) * (1 - p) ^ M = (1 - (1 - p) ^ M) / p := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hsum : (∑ k ∈ Finset.range M, ((k : ℝ) + 1) * p * (1 - p) ^ k) =
        (1 - (1 - p) ^ M) / p - (M : ℝ) * (1 - p) ^ M := by
      linarith [ih]
    rw [hsum]
    push_cast
    field_simp
    ring

/-- arXiv:1605.03590v2, Theorem 2 (p.18, Eq. (E4)): with per-attempt success
probability `2^{-n}`, the expected number of rotations performed before a failure
occurs is `2^n (1 - (1 - 2^{-n})^M)`. -/
theorem theorem2_par_expected_rotations (n M : ℕ) :
    (∑ k ∈ Finset.range M,
        ((k : ℝ) + 1) * (1 / (2 : ℝ) ^ n) * (1 - 1 / (2 : ℝ) ^ n) ^ k) +
        (M : ℝ) * (1 - 1 / (2 : ℝ) ^ n) ^ M =
      (2 : ℝ) ^ n * (1 - (1 - 1 / (2 : ℝ) ^ n) ^ M) := by
  have hp : (1 / (2 : ℝ) ^ n) ≠ 0 := by positivity
  rw [truncated_geometric_expectation (1 / (2 : ℝ) ^ n) hp M]
  have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
  field_simp
  try ring

end Qatlib.Papers.ReactionMech16.MainResults.Source
