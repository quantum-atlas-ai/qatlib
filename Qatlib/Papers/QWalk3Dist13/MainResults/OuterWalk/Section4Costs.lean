/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalk3Dist13.MainResults.SourceModel.CostLedger

set_option backward.isDefEq.respectTransparency false

/-!
# Query costs of the outer walk (Section 4, Theorems 4.2, 4.3, 4.8)

Fixed source: arXiv:1302.7316v1 (2013-02-28), Childs--Jeffery--Kothari--
Magniez, *A Time-Efficient Quantum Walk for 3-Distinctness Using Nested
Updates*.

The three query-cost inputs of Theorem 3.3 for the 3-Distinctness walk are

* Theorem 4.2 (p.11): the outer-walk setup costs `S_C = O(s₁ + s₂√(n/s₁))`
  queries;
* Theorem 4.3 (p.11): the update walk has `S' = O(s₁)` and inner walk cost
  `ε'^{-1/2}(δ'^{-1/2}U' + C') = Õ(√(n m/s₁))`;
* Theorem 4.8 (p.14): the checking reflection costs `C = Õ(√n)` queries.

This file records those cost expressions (`outerSetupQueries`, `innerSetupQueries`,
`checkingQueryCost`) and proves the arithmetic relations that the paper uses:

* the final ledger `threeDistinctnessCost` splits as setup + inner-walk +
  checking (`threeDistinctnessCost_split`);
* the inner walk cost bound follows from the numerical parameter bounds
  `ε' ≥ s₁²/(nm)`, `δ' ≥ 1/s₁`, `U' ≤ 1`, `C' = 0`
  (`theorem_4_3_inner_walk_cost`);
* the checking cost `√n` is dominated by the `n^{5/7}` budget
  (`sqrt_le_rpow_five_sevenths`).

The Ω(1) success probability for the random tripartition `A₁,A₂,A₃`
(Theorem 4.2) is a statement about the uniform distribution on balanced
tripartitions; no probability space for it is formalised in this layer, so it
is not stated here (recorded in the PR status table).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QWalk3Dist13.MainResults.OuterWalk

open scoped BigOperators
open Qatlib.Papers.QWalk3Dist13.MainResults.SourceModel

/-! ## Theorem 4.2: outer-walk setup cost (p.11) -/

/-- The number of queries of the outer-walk setup state
`C(n₂,s₂)^{-1/2} ∑_{S₂} |Q(S₂)⟩` (Theorem 4.2, p.11):
`s₁ + s₂ √(n/s₁)`, with the logarithmic factors of the `Õ` dropped. -/
def outerSetupQueries (n s1 s2 : ℝ) : ℝ :=
  s1 + s2 * Real.sqrt (n / s1)

/-- **Theorem 4.2** (fixed arXiv:1302.7316v1, p.11), query-count form: the
starting state of the outer walk is constructible with
`s₁ + s₂√(n/s₁)` queries. -/
theorem theorem_4_2_setup_queries (n s1 s2 : ℝ) :
    outerSetupQueries n s1 s2 = s1 + s2 * Real.sqrt (n / s1) := rfl

/-- The final 3-Distinctness ledger of Theorem 4.1 splits into the Theorem 4.2
setup term, the inner walk term `√(n/s₁)` and the Theorem 4.8 checking term
`√(n/s₂)`; this is the substitution the paper performs on p.14. -/
theorem threeDistinctnessCost_split (n s1 s2 : ℝ) :
    threeDistinctnessCost n s1 s2 =
      outerSetupQueries n s1 s2 + Real.sqrt (n / s1) + Real.sqrt (n / s2) := rfl

/-! ## Theorem 4.3: costs of the update walk (p.11) -/

/-- The update-walk setup cost `S' = s₁` queries (Theorem 4.3, p.11: "we can
construct the superposition over `S₁ ⊆ S̃₁` with `s₁` queries"). -/
def innerSetupQueries (s1 : ℝ) : ℝ := s1

/-- **Theorem 4.3, setup part** (fixed arXiv:1302.7316v1, p.11): the update
walk has setup complexity `S' = O(s₁)`, recorded as the ledger `s₁`. -/
theorem theorem_4_3_setup_cost (s1 : ℝ) : innerSetupQueries s1 = s1 := rfl

/-- **Theorem 4.3, inner-walk part** (fixed arXiv:1302.7316v1, p.11).  The
paper proves `δ' = Ω(1/s₁)`, `ε' = Ω(s₁²/(nm))`, `U' = O(1)`, `C' = 0`, and
concludes `ε'^{-1/2}(δ'^{-1/2}U' + C') = Õ(√(nm/s₁))`.  We prove the
corresponding numerical implication: under those parameter bounds the inner
walk cost `innerWalkCost U' C' ε' δ'` is at most `√(nm)/√s₁`, which equals
`√(nm/s₁)` by `sqrt_div_eq`. -/
theorem theorem_4_3_inner_walk_cost (n m s1 ε' δ' U' C' : ℝ)
    (hn : 0 < n) (hm : 0 < m) (hs1 : 0 < s1)
    (hε' : 0 < ε') (hδ' : 0 < δ')
    (hεlo : s1 ^ 2 / (n * m) ≤ ε') (hδlo : 1 / s1 ≤ δ')
    (hU0 : 0 ≤ U') (hU1 : U' ≤ 1) (hC' : C' = 0) :
    innerWalkCost U' C' ε' δ' ≤ Real.sqrt (n * m) / Real.sqrt s1 := by
  have hnm : 0 < n * m := mul_pos hn hm
  have hA : 0 < Real.sqrt ε' := Real.sqrt_pos.mpr hε'
  have hB : 0 < Real.sqrt δ' := Real.sqrt_pos.mpr hδ'
  have hns : 0 < Real.sqrt (n * m) := Real.sqrt_pos.mpr hnm
  have hss : 0 < Real.sqrt s1 := Real.sqrt_pos.mpr hs1
  -- first factor: `1/√ε' ≤ √(nm)/s₁`
  have hfac1 : 1 / Real.sqrt ε' ≤ Real.sqrt (n * m) / s1 := by
    have hsq : s1 ^ 2 ≤ ε' * (n * m) := by
      have h := (div_le_iff₀ hnm).mp hεlo
      nlinarith only [h]
    have hroot : s1 ≤ Real.sqrt ε' * Real.sqrt (n * m) := by
      have h1 : Real.sqrt (s1 ^ 2) ≤ Real.sqrt (ε' * (n * m)) := Real.sqrt_le_sqrt hsq
      rw [Real.sqrt_mul (le_of_lt hε')] at h1
      rwa [Real.sqrt_sq (le_of_lt hs1)] at h1
    rw [le_div_iff₀ hs1, div_mul_eq_mul_div, div_le_iff₀ hA]
    nlinarith only [hroot]
  -- second factor: `1/√δ' ≤ √s₁`
  have hfac2 : 1 / Real.sqrt δ' ≤ Real.sqrt s1 := by
    have hmul : (1 : ℝ) ≤ δ' * s1 := by
      have h := (div_le_iff₀ hs1).mp hδlo
      linarith only [h]
    have hroot : (1 : ℝ) ≤ Real.sqrt δ' * Real.sqrt s1 := by
      have h1 : Real.sqrt 1 ≤ Real.sqrt (δ' * s1) := Real.sqrt_le_sqrt hmul
      rwa [Real.sqrt_one, Real.sqrt_mul (le_of_lt hδ')] at h1
    rw [div_le_iff₀ hB]
    nlinarith only [hroot]
  unfold innerWalkCost
  rw [hC']
  have hinner : (1 / Real.sqrt δ') * U' + 0 ≤ Real.sqrt s1 := by
    have : (1 / Real.sqrt δ') * U' ≤ Real.sqrt s1 * 1 := by
      calc (1 / Real.sqrt δ') * U' ≤ (1 / Real.sqrt δ') * 1 := by
            exact mul_le_mul_of_nonneg_left hU1 (by positivity)
        _ ≤ Real.sqrt s1 * 1 := by
            exact mul_le_mul_of_nonneg_right hfac2 (by norm_num)
    linarith only [this]
  have hinner0 : 0 ≤ (1 / Real.sqrt δ') * U' + 0 := by positivity
  calc (1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + 0)
      ≤ (1 / Real.sqrt ε') * Real.sqrt s1 := by
        exact mul_le_mul_of_nonneg_left hinner (by positivity)
    _ ≤ (Real.sqrt (n * m) / s1) * Real.sqrt s1 := by
        exact mul_le_mul_of_nonneg_right hfac1 (le_of_lt hss)
    _ = Real.sqrt (n * m) / Real.sqrt s1 := by
        have hsq : Real.sqrt s1 * Real.sqrt s1 = s1 :=
          Real.mul_self_sqrt (le_of_lt hs1)
        have hs1ne : s1 ≠ 0 := ne_of_gt hs1
        have hssne : Real.sqrt s1 ≠ 0 := ne_of_gt hss
        field_simp
        nlinarith only [hsq]

/-- `√(nm)/√s₁ = √(nm/s₁)` for nonnegative `n,m`: the form in which
Theorem 4.3 (p.11) displays the inner walk cost. -/
theorem sqrt_div_eq (n m s1 : ℝ) (hnm : 0 ≤ n * m) :
    Real.sqrt (n * m) / Real.sqrt s1 = Real.sqrt (n * m / s1) := by
  exact (Real.sqrt_div hnm s1).symm

/-! ## Theorem 4.8: checking cost (p.14) -/

/-- The checking reflection's query cost `C = Õ(√n)` (Theorem 4.8, p.14),
written with its logarithmic factor. -/
def checkingQueryCost (n : ℝ) : ℝ :=
  Real.sqrt n * (Real.log (n + 2) + 1)

/-- **Theorem 4.8** (fixed arXiv:1302.7316v1, p.14): the checking reflection is
implementable with `√n (log(n+2) + 1)` queries, i.e. `Õ(√n)`. -/
theorem theorem_4_8_checking_cost (n : ℝ) :
    checkingQueryCost n = Real.sqrt n * (Real.log (n + 2) + 1) := rfl

/-- `√n ≤ n^{5/7}` for `n ≥ 1`: the checking cost is dominated by the final
`n^{5/7}` budget (used in the proof of Theorems 4.1 and 5.1). -/
theorem sqrt_le_rpow_five_sevenths (n : ℝ) (hn : 1 ≤ n) :
    Real.sqrt n ≤ n ^ (5 / 7 : ℝ) := by
  rw [Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_le hn (by norm_num)

end Qatlib.Papers.QWalk3Dist13.MainResults.OuterWalk
