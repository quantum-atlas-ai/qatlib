/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.DLoNonvacuityStat
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith

/-!
# Eventual positivity of degree thresholds

Proves that the natural floor of `n ^ p / 10` is eventually at least one for every positive real
exponent `p`. The result establishes `DLoNonvacuity` for both the variable exponent `1 - δ` and
the fixed exponent `6 / 7`, ensuring positive low-degree thresholds in graph-search estimates;
see [Ambainis2005].

## Main statements

* `dLo_positive_exponent`: For every positive real exponent `p`, there is a positive natural
  threshold beyond which `Nat.floor ((n : ℝ) ^ p / 10) ≥ 1`.
* `dLoNonvacuity_answer`: Establishes eventual positivity of the low-degree thresholds with
  exponents `1 - δ` for `0 < δ < 1` and `6 / 7`.

## References

* [Ambainis, 2005][Ambainis2005]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.WalkSearch.Primitives

/-- For every positive real exponent `p`, there is a positive natural threshold beyond which
`Nat.floor ((n : ℝ) ^ p / 10) ≥ 1`. -/
theorem dLo_positive_exponent (p : ℝ) (hp : 0 < p) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → 1 ≤ Nat.floor ((n : ℝ) ^ p / 10) := by
  obtain ⟨M, hM⟩ := exists_nat_gt ((10 : ℝ) ^ p⁻¹)
  refine ⟨max M 1, le_max_right _ _, ?_⟩
  intro n hn
  have hbase : (10 : ℝ) ^ p⁻¹ ≤ (n : ℝ) :=
    hM.le.trans (Nat.cast_le.mpr ((le_max_left M 1).trans hn))
  have hpow : (10 : ℝ) ≤ (n : ℝ) ^ p :=
    (Real.rpow_inv_le_iff_of_pos (by norm_num) (Nat.cast_nonneg n) hp).mp hbase
  exact Nat.one_le_floor_iff _ |>.mpr (by linarith)

/-- Establishes eventual positivity of the low-degree thresholds with exponents `1 - δ` for `0 <
δ < 1` and `6 / 7`. -/
theorem dLoNonvacuity_answer : DLoNonvacuity := by
  constructor
  · intro δ _hδ hδ
    exact dLo_positive_exponent (1 - δ) (by linarith)
  · exact dLo_positive_exponent ((6 : ℝ) / 7) (by norm_num)

end Qatlib.Concepts.WalkSearch.Primitives
