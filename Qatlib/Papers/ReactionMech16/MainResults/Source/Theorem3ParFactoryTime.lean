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
# Theorem 3: average time per rotation of the factory-based PAR strategy

Source: arXiv:1605.03590v2, Appendix E, Theorem 3 (p.19, Eq. (E5)).
The paper's proof writes the expected cost as
`∑_{j=1}^{n} j / 2^j + (C + n) / 2^n`,
where the first sum is the expected number of PAR attempts that succeed and the
second term models a failure (probability `2^{-n}`) costing `n` further attempts
plus `C` T gates for the fallback synthesis.  Summing the geometric series gives
`2 - (n + 2) / 2^n`, hence the displayed average time
`(2 - (n + 2) / 2^n) + (C + n) / 2^n`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.ReactionMech16.MainResults.Source

/-- arXiv:1605.03590v2, Eq. (E5): the weighted geometric series
`∑_{j=1}^{n} j / 2^j = 2 - (n + 2) / 2^n`.
Written with a zero-based `range` index: the `j = k + 1` term is `(k+1)/2^{k+1}`. -/
theorem weighted_geometric_identity (n : ℕ) :
    (∑ k ∈ Finset.range n, ((k : ℝ) + 1) / (2 : ℝ) ^ (k + 1)) =
      2 - ((n : ℝ) + 2) / (2 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    field_simp
    push_cast
    ring

/-- arXiv:1605.03590v2, Theorem 3 (p.19): the average time required per rotation for
the factory-based PAR strategy, with each PAR application costing at most one T gate
and all Clifford operations free, is `(2 - (n+2)/2^n) + (C+n)/2^n`.  Here `C` is the
T-gate cost of synthesizing one rotation and `n` is the number of cached corrections. -/
theorem theorem3_par_factory_average_time (n : ℕ) (C : ℝ) :
    (∑ k ∈ Finset.range n, ((k : ℝ) + 1) / (2 : ℝ) ^ (k + 1)) +
        (C + (n : ℝ)) / (2 : ℝ) ^ n =
      (2 - ((n : ℝ) + 2) / (2 : ℝ) ^ n) + (C + (n : ℝ)) / (2 : ℝ) ^ n := by
  rw [weighted_geometric_identity]

end Qatlib.Papers.ReactionMech16.MainResults.Source
