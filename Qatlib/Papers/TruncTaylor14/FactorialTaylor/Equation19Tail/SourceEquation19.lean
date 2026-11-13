/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.FactorialTaylor.FactorialTaylorSimulation

set_option backward.isDefEq.respectTransparency false

/-!
# Source Eq. (19) — the factorial Taylor tail at `ln 2` is `≤ ε/r`

arXiv:1412.4687v1, p. 3, Eq. (19).  With `T/r = ln 2` the per-segment
normalization `Σ_{k≤K} ln(2)^k/k!` leaves the tail

`Σ_{k=K+1}^∞ ln(2)^k / k! ≤ ε/r`.

The established scalar tail theorem `factorialTaylor_tail` bounds every unit-interval
tail by twice its first omitted term,
`Σ_{j} θ^{K+1+j}/(K+1+j)! ≤ 2 θ^{K+1}/(K+1)!` for `0 ≤ θ ≤ 1`.  Taking
`θ = ln 2 ∈ [0,1]` gives Eq. (19) as soon as the cutoff `K` is chosen so that
`2·ln(2)^{K+1}/(K+1)! ≤ ε/r`, which is exactly the source's "so that" clause.

The tail theorem used here is
`Qatlib.Papers.TruncTaylor14.FactorialTaylor.factorialTaylor_tail`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.TruncTaylor14.FactorialTaylor.Equation19Tail

open Qatlib.Concepts.CoherentSim.FactorialTaylor

/-- `ln 2` lies in the unit interval, the hypothesis of the tail bound. -/
theorem log_two_mem_unit_interval : 0 ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  constructor
  · exact Real.log_nonneg (by norm_num)
  · have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith

/-- arXiv:1412.4687v1 Eq. (19), p. 3: the reindexed tail
`Σ_{j} ln(2)^{K+1+j}/(K+1+j)!` is at most `ε/r` once the cutoff budget
`2·ln(2)^{K+1}/(K+1)! ≤ ε/r` holds. -/
theorem source_equation19 (K : ℕ) (ε r : ℝ)
    (hbudget :
      2 * (Real.log 2) ^ (K + 1) / (((K + 1).factorial : ℕ) : ℝ) ≤ ε / r) :
    (∑' j : ℕ, (Real.log 2) ^ (K + 1 + j) /
      (((K + 1 + j).factorial : ℕ) : ℝ)) ≤ ε / r := by
  have htail := factorialTaylor_tail (Real.log 2) K
    log_two_mem_unit_interval.1 log_two_mem_unit_interval.2
  exact htail.2.trans hbudget

/-- Eq. (19) written as the difference between the full exponential series and
its first `K+1` terms: this is the paper's displayed form
`Σ_{k=K+1}^∞ ln(2)^k/k!` (the tail sum is reindexed as `i + (K+1)`). -/
theorem source_equation19_eq_full_sub_partial (K : ℕ) :
    (∑' i : ℕ, (Real.log 2) ^ i / ((i.factorial : ℕ) : ℝ)) -
        ∑ i ∈ Finset.range (K + 1), (Real.log 2) ^ i / ((i.factorial : ℕ) : ℝ) =
      ∑' i : ℕ, (Real.log 2) ^ (i + (K + 1)) /
        (((i + (K + 1)).factorial : ℕ) : ℝ) := by
  have hsum : Summable (fun i : ℕ => (Real.log 2) ^ i / ((i.factorial : ℕ) : ℝ)) :=
    Real.summable_pow_div_factorial (Real.log 2)
  have h := hsum.sum_add_tsum_nat_add (K + 1)
  linarith

end Qatlib.Papers.TruncTaylor14.FactorialTaylor.Equation19Tail
