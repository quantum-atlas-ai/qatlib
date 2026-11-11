/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Cost ledger of the nested-update quantum walk

Fixed source: arXiv:1302.7316v1 (2013-02-28), Childs--Jeffery--Kothari--
Magniez, *A Time-Efficient Quantum Walk for 3-Distinctness Using Nested
Updates*.

This file records the cost expressions of the paper and proves the arithmetic
that the paper performs on them:

* `walkSearchCost S U C δ ε = S + ε^{-1/2}(δ^{-1/2} U + C)` --- Theorem 3.1,
  p.7 (and Theorem 2.1 of [MNRS11]);
* `innerWalkCost U' C' ε' δ' = ε'^{-1/2}(δ'^{-1/2} U' + C')` --- the inner
  update-walk cost, proof of Theorem 3.3, p.9;
* `nestedUpdateCost` --- the nested-update expression displayed in the
  statement of Theorem 3.3, p.8;
* `theorem_3_3_cost` --- the passage from the quantisation of `P` (whose
  setup/update/checking costs are `S_C + S' + inner`, `T + inner`, `C_C`,
  proof of Theorem 3.3, p.9) to the displayed nested formula, up to the factor
  `2` that the paper absorbs in the `Õ`;
* `threeDistinctnessCost` --- the final ledger of the proof of Theorem 4.1,
  p.14, `s₁ + s₂√(n/s₁) + √(n/s₁) + √(n/s₂)`;
* `threeDistinctnessCost_optimal` --- substituting `s₁ = n^{5/7}`,
  `s₂ = n^{4/7}` (p.14) turns that ledger into `O(n^{5/7})`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QWalk3Dist13.MainResults.SourceModel

open scoped BigOperators

/-! ## The walk-search and nested-update cost expressions -/

/-- Theorem 3.1 (p.7): the cost `S + ε^{-1/2}(δ^{-1/2} U + C)` of the quantised
walk search. -/
def walkSearchCost (S U C δ ε : ℝ) : ℝ :=
  S + (1 / Real.sqrt ε) * ((1 / Real.sqrt δ) * U + C)

/-- The inner walk cost `ε'^{-1/2}(δ'^{-1/2} U' + C')` appearing in the proof of
Theorem 3.3 (p.8-9). -/
def innerWalkCost (U' C' ε' δ' : ℝ) : ℝ :=
  (1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + C')

/-- Theorem 3.3 (p.8): the nested-update cost displayed in the statement,
before the logarithmic factors of the `Õ`. -/
def nestedUpdateCost (SC S' T CC U' C' δ ε ε' δ' : ℝ) : ℝ :=
  SC + S' + (1 / Real.sqrt ε) * ((1 / Real.sqrt δ) *
    ((1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + C') + T) + CC)

/-- The inner walk cost is nonnegative when all of its ingredients are
(used in the proof of Theorem 3.3, p.9). -/
theorem innerWalkCost_nonneg {U' C' ε' δ' : ℝ}
    (hU : 0 ≤ U') (hC : 0 ≤ C') (hε : 0 < ε') (hδ : 0 < δ') :
    0 ≤ innerWalkCost U' C' ε' δ' := by
  have hεs : 0 < Real.sqrt ε' := Real.sqrt_pos.mpr hε
  have hδs : 0 < Real.sqrt δ' := Real.sqrt_pos.mpr hδ
  unfold innerWalkCost
  positivity

/-- The quantisation of the walk `P` with data structure `D` has setup cost
`S_C + S' + inner`, update cost `T + inner` and checking cost `C_C` (proof of
Theorem 3.3, p.9).  Feeding these into Theorem 3.1 leaves exactly the nested
expression plus one copy of the inner cost. -/
theorem nested_cost_eq (SC S' T CC U' C' δ ε ε' δ' : ℝ) :
    walkSearchCost (SC + S' + innerWalkCost U' C' ε' δ')
        (T + innerWalkCost U' C' ε' δ') CC δ ε =
      nestedUpdateCost SC S' T CC U' C' δ ε ε' δ' +
        innerWalkCost U' C' ε' δ' := by
  unfold walkSearchCost nestedUpdateCost innerWalkCost
  ring

/-- The arithmetic step of Theorem 3.3 (p.9): when the marked mass `ε` and the
spectral gap `δ` are at most one and all costs are nonnegative, the search cost
of the data-augmented walk is at most twice the displayed nested-update
expression.  (The paper writes the two as equal under `Õ`; the factor `2` is
the explicit form of that absorption.) -/
theorem theorem_3_3_cost (SC S' T CC U' C' δ ε ε' δ' : ℝ)
    (hSC : 0 ≤ SC) (hS' : 0 ≤ S') (hT : 0 ≤ T) (hCC : 0 ≤ CC)
    (hU : 0 ≤ U') (hC : 0 ≤ C')
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hε' : 0 < ε') (hδ' : 0 < δ') :
    walkSearchCost (SC + S' + innerWalkCost U' C' ε' δ')
        (T + innerWalkCost U' C' ε' δ') CC δ ε ≤
      2 * nestedUpdateCost SC S' T CC U' C' δ ε ε' δ' := by
  rw [nested_cost_eq]
  have hI : 0 ≤ innerWalkCost U' C' ε' δ' :=
    innerWalkCost_nonneg hU hC hε' hδ'
  have hεs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hδs : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hinvε : 1 ≤ 1 / Real.sqrt ε := by
    rw [le_div_iff₀ hεs]
    have hsq : Real.sqrt ε ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt hε1
    simpa using hsq
  have hinvδ : 1 ≤ 1 / Real.sqrt δ := by
    rw [le_div_iff₀ hδs]
    have hsq : Real.sqrt δ ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt hδ1
    simpa using hsq
  -- work with the explicit inner cost so that the two sides of the final
  -- comparison are syntactically identical to the unfolded `nestedUpdateCost`
  have hinner : (1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + C') ≤
      (1 / Real.sqrt ε) *
        ((1 / Real.sqrt δ) *
          ((1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + C') + T) + CC) := by
    have hIex : 0 ≤ (1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + C') := by
      simpa only [innerWalkCost] using hI
    have h1 : 0 < 1 / Real.sqrt δ := div_pos one_pos hδs
    have h2 : 0 ≤ (1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + C') + T := by
      linarith only [hIex, hT]
    have hA : (1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + C') ≤
        (1 / Real.sqrt δ) *
          ((1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + C') + T) := by
      calc (1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + C')
          ≤ (1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + C') + T :=
            le_add_of_nonneg_right hT
        _ = 1 * ((1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + C') + T) :=
            (one_mul _).symm
        _ ≤ (1 / Real.sqrt δ) *
              ((1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + C') + T) :=
            mul_le_mul_of_nonneg_right hinvδ h2
    have hB : (1 / Real.sqrt δ) *
          ((1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + C') + T) ≤
        (1 / Real.sqrt δ) *
          ((1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + C') + T) + CC :=
      le_add_of_nonneg_right hCC
    have hM0 : 0 ≤ (1 / Real.sqrt δ) *
        ((1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + C') + T) :=
      mul_nonneg (le_of_lt h1) h2
    have hXY0 : 0 ≤ (1 / Real.sqrt δ) *
        ((1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + C') + T) + CC := by
      linarith only [hM0, hCC]
    calc (1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + C')
        ≤ (1 / Real.sqrt δ) *
            ((1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + C') + T) + CC :=
          le_trans hA hB
      _ = 1 * ((1 / Real.sqrt δ) *
            ((1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + C') + T) + CC) :=
          (one_mul _).symm
      _ ≤ (1 / Real.sqrt ε) * ((1 / Real.sqrt δ) *
            ((1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + C') + T) + CC) :=
          mul_le_mul_of_nonneg_right hinvε hXY0
  unfold nestedUpdateCost
  unfold innerWalkCost
  have h1 : 0 < 1 / Real.sqrt δ := div_pos one_pos hδs
  have hIex : 0 ≤ (1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + C') := by
    simpa only [innerWalkCost] using hI
  have h2 : 0 ≤ (1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + C') + T := by
    linarith only [hIex, hT]
  have hM0 : 0 ≤ (1 / Real.sqrt δ) *
      ((1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + C') + T) :=
    mul_nonneg (le_of_lt h1) h2
  have hX0 : 0 ≤ (1 / Real.sqrt ε) * ((1 / Real.sqrt δ) *
      ((1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + C') + T) + CC) := by
    have hXY0 : 0 ≤ (1 / Real.sqrt δ) *
        ((1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + C') + T) + CC := by
      linarith only [hM0, hCC]
    exact mul_nonneg (le_of_lt (div_pos one_pos hεs)) hXY0
  have hXD : (1 / Real.sqrt ε) * ((1 / Real.sqrt δ) *
        ((1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + C') + T) + CC) ≤
      SC + S' + (1 / Real.sqrt ε) * ((1 / Real.sqrt δ) *
        ((1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + C') + T) + CC) := by
    linarith only [hSC, hS']
  have hID : (1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + C') ≤
      SC + S' + (1 / Real.sqrt ε) * ((1 / Real.sqrt δ) *
        ((1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + C') + T) + CC) :=
    le_trans hinner hXD
  have hD0 : 0 ≤ SC + S' + (1 / Real.sqrt ε) * ((1 / Real.sqrt δ) *
      ((1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + C') + T) + CC) := by
    linarith only [hSC, hS', hX0]
  linarith only [hID, hD0]

/-! ## The final 3-Distinctness ledger of Theorem 4.1 (p.14) -/

/-- The cost `s₁ + s₂√(n/s₁) + √(n/s₁) + √(n/s₂)` obtained in the proof of
Theorem 4.1 (p.14) after substituting the costs of Theorems 4.2, 4.3, 4.8 and
Corollary 4.7 into the Theorem 3.3 expression.  Logarithmic factors are
dropped. -/
def threeDistinctnessCost (n s1 s2 : ℝ) : ℝ :=
  s1 + s2 * Real.sqrt (n / s1) + Real.sqrt (n / s1) + Real.sqrt (n / s2)

/-- Section 5 (p.19) has the same ledger for time complexity: the only extra
term is `T = Õ(m) = Õ(s₁/n)`, which is absorbed. -/
def threeDistinctnessTimeCost (n s1 s2 : ℝ) : ℝ :=
  threeDistinctnessCost n s1 s2

/-- `n / n^(5/7) = n^(2/7)` for positive `n` (Theorem 4.1 final step, p.14). -/
theorem div_rpow_five_sevenths {n : ℝ} (hn : 0 < n) :
    n / n ^ (5 / 7 : ℝ) = n ^ (2 / 7 : ℝ) := by
  have h := Real.rpow_sub (x := n) hn (y := 1) (z := (5 / 7 : ℝ))
  rw [Real.rpow_one] at h
  rw [← h]
  norm_num

/-- `√(n^(2/7)) = n^(1/7)` for positive `n` (Theorem 4.1 final step, p.14). -/
theorem sqrt_rpow_two_sevenths {n : ℝ} (hn : 0 < n) :
    Real.sqrt (n ^ (2 / 7 : ℝ)) = n ^ (1 / 7 : ℝ) := by
  rw [Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul (le_of_lt hn)]
  norm_num

/-- `n^(4/7) · n^(1/7) = n^(5/7)` for nonnegative `n` (Theorem 4.1 final step, p.14). -/
theorem rpow_four_mul_rpow_one {n : ℝ} (hn : 0 ≤ n) :
    n ^ (4 / 7 : ℝ) * n ^ (1 / 7 : ℝ) = n ^ (5 / 7 : ℝ) := by
  rw [← Real.rpow_add' hn (by norm_num)]
  norm_num

/-- `n^(1/7) ≤ n^(5/7)` for `n ≥ 1` (Theorem 4.1 final step, p.14). -/
theorem rpow_one_le_five {n : ℝ} (hn : 1 ≤ n) :
    n ^ (1 / 7 : ℝ) ≤ n ^ (5 / 7 : ℝ) :=
  Real.rpow_le_rpow_of_exponent_le hn (by norm_num)

/-- `n^(3/14) ≤ n^(5/7)` for `n ≥ 1` (Theorem 4.1 final step, p.14). -/
theorem rpow_three_le_five {n : ℝ} (hn : 1 ≤ n) :
    n ^ (3 / 14 : ℝ) ≤ n ^ (5 / 7 : ℝ) :=
  Real.rpow_le_rpow_of_exponent_le hn (by norm_num)

/-- `√(n / n^(5/7)) = n^(1/7)` for positive `n` (Theorem 4.1 final step, p.14). -/
theorem sqrt_div_five {n : ℝ} (hn : 0 < n) :
    Real.sqrt (n / n ^ (5 / 7 : ℝ)) = n ^ (1 / 7 : ℝ) := by
  rw [div_rpow_five_sevenths hn, sqrt_rpow_two_sevenths hn]

/-- `√(n / n^(4/7)) = n^(3/14)` for positive `n` (Theorem 4.1 final step, p.14). -/
theorem sqrt_div_four {n : ℝ} (hn : 0 < n) :
    Real.sqrt (n / n ^ (4 / 7 : ℝ)) = n ^ (3 / 14 : ℝ) := by
  have h : n / n ^ (4 / 7 : ℝ) = n ^ (3 / 7 : ℝ) := by
    have h := Real.rpow_sub (x := n) hn (y := 1) (z := (4 / 7 : ℝ))
    rw [Real.rpow_one] at h
    rw [← h]
    norm_num
  rw [h, Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hn)]
  norm_num

/-- **Theorem 4.1, final step** (fixed arXiv:1302.7316v1, p.14): with
`s₁ = n^{5/7}` and `s₂ = n^{4/7}` the ledger `threeDistinctnessCost` is at most
`4 n^{5/7}`.  This is the paper's "setting s₁ = n^{5/7} and s₂ = n^{4/7} gives
query complexity Õ(n^{5/7})". -/
theorem threeDistinctnessCost_optimal (n : ℝ) (hn : 1 ≤ n) :
    threeDistinctnessCost n (n ^ (5 / 7 : ℝ)) (n ^ (4 / 7 : ℝ)) ≤
      4 * n ^ (5 / 7 : ℝ) := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have h1 : Real.sqrt (n / n ^ (5 / 7 : ℝ)) = n ^ (1 / 7 : ℝ) :=
    sqrt_div_five hn0
  have h2 : Real.sqrt (n / n ^ (4 / 7 : ℝ)) = n ^ (3 / 14 : ℝ) :=
    sqrt_div_four hn0
  have h3 : n ^ (4 / 7 : ℝ) * n ^ (1 / 7 : ℝ) = n ^ (5 / 7 : ℝ) :=
    rpow_four_mul_rpow_one (le_of_lt hn0)
  have h4 : n ^ (1 / 7 : ℝ) ≤ n ^ (5 / 7 : ℝ) := rpow_one_le_five hn
  have h5 : n ^ (3 / 14 : ℝ) ≤ n ^ (5 / 7 : ℝ) := rpow_three_le_five hn
  have hpos : 0 ≤ n ^ (5 / 7 : ℝ) := Real.rpow_nonneg (le_of_lt hn0) _
  unfold threeDistinctnessCost
  rw [h1, h2]
  -- ledger = n^(5/7) + n^(5/7) + n^(1/7) + n^(3/14)
  have e : n ^ (5 / 7 : ℝ) + n ^ (4 / 7 : ℝ) * n ^ (1 / 7 : ℝ) +
        n ^ (1 / 7 : ℝ) + n ^ (3 / 14 : ℝ) =
      n ^ (5 / 7 : ℝ) + n ^ (5 / 7 : ℝ) + n ^ (1 / 7 : ℝ) +
        n ^ (3 / 14 : ℝ) := by rw [h3]
  rw [e]
  linarith only [h4, h5, hpos]

/-- **Theorem 4.1, parameter form** (p.14): there are parameters `s₁,s₂`
(concretely `s₁ = n^{5/7}`, `s₂ = n^{4/7}`) for which the ledger of the paper's
algorithm is at most `4 n^{5/7}`. -/
theorem theorem_4_1_parameters (n : ℝ) (hn : 1 ≤ n) :
    ∃ s1 s2 : ℝ, 0 < s1 ∧ 0 < s2 ∧ n ^ (4 / 7 : ℝ) = s2 ∧
      threeDistinctnessCost n s1 s2 ≤ 4 * n ^ (5 / 7 : ℝ) := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  refine ⟨n ^ (5 / 7 : ℝ), n ^ (4 / 7 : ℝ), ?_, ?_, rfl, ?_⟩
  · exact Real.rpow_pos_of_pos hn0 _
  · exact Real.rpow_pos_of_pos hn0 _
  · exact threeDistinctnessCost_optimal n hn

/-- **Theorem 5.1, final step** (p.19): the time ledger at
`s₁ = n^{5/7}, s₂ = n^{4/7}` is `O(n^{5/7})` (the extra `T = Õ(m)` term is
absorbed by the same bound in the paper). -/
theorem threeDistinctnessTimeCost_optimal (n : ℝ) (hn : 1 ≤ n) :
    threeDistinctnessTimeCost n (n ^ (5 / 7 : ℝ)) (n ^ (4 / 7 : ℝ)) ≤
      4 * n ^ (5 / 7 : ℝ) :=
  threeDistinctnessCost_optimal n hn

end Qatlib.Papers.QWalk3Dist13.MainResults.SourceModel
