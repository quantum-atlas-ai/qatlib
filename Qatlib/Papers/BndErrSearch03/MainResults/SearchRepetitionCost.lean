/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Qatlib.Concepts.SearchStopping.RestartLaw.Section3RestartExpectedSubgoalTigh

/-!
# Recurrence and repetition costs for bounded-error search

This module proves scalar cost estimates for the bounded-error search analysis of
[HoyerMoscaDeWolf2003]. `RoundCostLaw` and `PaperCostLaw` specify cost recurrences;
`query_cost_le_sqrt` and `paper_query_cost_le_sqrt` bound a scheduled round by `13 * Real.sqrt
n` under the corresponding recurrence hypotheses.

`bounded_error_expected_cost_le_sqrt` bounds the geometric restart series when the success
parameter is at least `1/576`. `totalCost` and `total_cost_le_sqrt` account for 1000 repetitions
of each scheduled round and a logarithmic verification term, while `thousand_repeat_success_ge`
bounds the scalar success expression for 1000 repetitions.

## Main statements

* `query_cost_le_sqrt`: a scheduled round cost bounded by `13 * Real.sqrt n`.
* `bounded_error_expected_cost_le_sqrt`: the conditional geometric restart cost bound.
* `total_cost_le_sqrt`: the square-root bound for the specified scalar total.

## References

* [Høyer et al., 2003][HoyerMoscaDeWolf2003]
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.BndErrSearch03.MainResults.SearchRepetitionCost

/-- The scalar cost conditions `C 1 ≤ 12` and `C (k + 1) ≤ 3 * C k + k` for every natural `k`. -/
def RoundCostLaw (C : ℕ → ℝ) : Prop :=
  C 1 ≤ 12 ∧ ∀ k : ℕ, C (k + 1) ≤ 3 * C k + (k : ℝ)

/-- Under `RoundCostLaw`, the strengthened bound `C (n + 1) + (n + 1) ≤ 13 * 3 ^ n` holds for
every natural `n`. -/
theorem round_cost_succ_aux (C : ℕ → ℝ) (hC : RoundCostLaw C) :
    ∀ n : ℕ, C (n + 1) + ((n + 1 : ℕ) : ℝ) ≤ 13 * 3 ^ n := by
  intro n
  induction n with
  | zero =>
    have h := hC.1
    norm_num
    linarith
  | succ n ih =>
    have hstep : C (n + 1 + 1) ≤ 3 * C (n + 1) + ((n + 1 : ℕ) : ℝ) := hC.2 (n + 1)
    have hpow : (3 : ℝ) ^ (n + 1) = 3 * 3 ^ n := by rw [pow_succ]; ring
    rw [hpow]
    have hc1 : ((n + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
    have hc2 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hc2] at hstep ih
    rw [hc1]
    nlinarith [ih, hstep]

/-- Under `RoundCostLaw`, round `m ≥ 1` has scalar cost at most `13 * 3 ^ (m - 1)`. -/
theorem round_cost_le (C : ℕ → ℝ) (hC : RoundCostLaw C) (m : ℕ) (hm : 1 ≤ m) :
    C m ≤ 13 * 3 ^ (m - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [show n + 1 - 1 = n by omega]
  have h := round_cost_succ_aux C hC n
  have hnn : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
  linarith

/-- Under `RoundCostLaw` and the schedule condition `9 ^ (m - 1) ≤ n`, round `m ≥ 1` has scalar
cost at most `13 * Real.sqrt n`. -/
theorem query_cost_le_sqrt (C : ℕ → ℝ) (hC : RoundCostLaw C) (m : ℕ) (hm : 1 ≤ m)
    (n : ℝ) (_hn : 0 < n) (hschedule : 9 ^ (m - 1) ≤ n) :
    C m ≤ 13 * Real.sqrt n := by
  have hcost := round_cost_le C hC m hm
  have h3le : (3 : ℝ) ^ (m - 1) ≤ Real.sqrt n := by
    have h9 : (9 : ℝ) ^ (m - 1) = ((3 : ℝ) ^ (m - 1)) ^ 2 := by
      calc (9 : ℝ) ^ (m - 1) = (3 ^ 2) ^ (m - 1) := by
            rw [show (9 : ℝ) = 3 ^ 2 by norm_num]
        _ = 3 ^ (2 * (m - 1)) := (pow_mul (3 : ℝ) 2 (m - 1)).symm
        _ = 3 ^ ((m - 1) * 2) := by rw [Nat.mul_comm]
        _ = ((3 : ℝ) ^ (m - 1)) ^ 2 := pow_mul (3 : ℝ) (m - 1) 2
    calc (3 : ℝ) ^ (m - 1)
        = Real.sqrt (((3 : ℝ) ^ (m - 1)) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ = Real.sqrt (9 ^ (m - 1)) := by rw [h9]
      _ ≤ Real.sqrt n := Real.sqrt_le_sqrt hschedule
  calc C m ≤ 13 * 3 ^ (m - 1) := hcost
    _ ≤ 13 * Real.sqrt n := mul_le_mul_of_nonneg_left h3le (by norm_num)

/-- Under the cost recurrence and schedule hypotheses, a success parameter `1/576 ≤ p ≤ 1`
bounds the displayed geometric restart cost series by `576 * (13 * Real.sqrt n)`. This is a
conditional expected-cost estimate for the analysis in [HoyerMoscaDeWolf2003]. -/
theorem bounded_error_expected_cost_le_sqrt
    (C : ℕ → ℝ) (hC : RoundCostLaw C) (_hCnn : ∀ m, 0 ≤ C m)
    (m : ℕ) (hm : 1 ≤ m) (n : ℝ) (hn : 0 < n) (hschedule : 9 ^ (m - 1) ≤ n)
    (p : ℝ) (hp : (1 / 576 : ℝ) ≤ p) (hp1 : p ≤ 1) :
    (∑' r : ℕ, ((r + 1 : ℕ) : ℝ) * C m * ((1 - p) ^ r * p))
      ≤ 576 * (13 * Real.sqrt n) := by
  have hp0 : 0 < p := by linarith
  rw [Qatlib.Concepts.SearchStopping.RestartLaw.geometric_restart_expectation
    p (C m) hp0 hp1]
  have hcost := query_cost_le_sqrt C hC m hm n hn hschedule
  rw [div_le_iff₀ hp0]
  have hsqrt_nn : (0 : ℝ) ≤ 13 * Real.sqrt n := by positivity
  have hp576 : (1 : ℝ) ≤ 576 * p := by linarith
  have hstep : 13 * Real.sqrt n ≤ (13 * Real.sqrt n) * (576 * p) := by
    have := mul_le_mul_of_nonneg_left hp576 hsqrt_nn
    simpa using this
  calc C m ≤ 13 * Real.sqrt n := hcost
    _ ≤ (13 * Real.sqrt n) * (576 * p) := hstep
    _ = 576 * (13 * Real.sqrt n) * p := by ring

/-- The scalar cost conditions `C 1 = 1` and `C (k + 1) ≤ 3 * C k + k` for every `k ≥ 1`. -/
def PaperCostLaw (C : ℕ → ℝ) : Prop :=
  C 1 = 1 ∧ ∀ k : ℕ, 1 ≤ k → C (k + 1) ≤ 3 * C k + (k : ℝ)

/-- Under `PaperCostLaw`, the strengthened bound `C (n + 1) + (n + 1) ≤ 13 * 3 ^ n` holds for
every natural `n`. -/
theorem paper_cost_succ_add_le (C : ℕ → ℝ) (hC : PaperCostLaw C) :
    ∀ n : ℕ, C (n + 1) + ((n + 1 : ℕ) : ℝ) ≤ 13 * 3 ^ n := by
  intro n
  induction n with
  | zero =>
    have h := hC.1
    norm_num
    linarith
  | succ n ih =>
    have hstep : C (n + 1 + 1) ≤ 3 * C (n + 1) + ((n + 1 : ℕ) : ℝ) :=
      hC.2 (n + 1) (by omega)
    have hpow : (3 : ℝ) ^ (n + 1) = 3 * 3 ^ n := by rw [pow_succ]; ring
    rw [hpow]
    have hc1 : ((n + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
    have hc2 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hc2] at hstep ih
    rw [hc1]
    nlinarith [ih, hstep]

/-- Under `PaperCostLaw`, round `m ≥ 1` has scalar cost at most `13 * 3 ^ (m - 1)`. -/
theorem paper_cost_le (C : ℕ → ℝ) (hC : PaperCostLaw C) (m : ℕ) (hm : 1 ≤ m) :
    C m ≤ 13 * 3 ^ (m - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [show n + 1 - 1 = n by omega]
  have h := paper_cost_succ_add_le C hC n
  have hnn : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
  linarith

/-- Under `PaperCostLaw` and the schedule condition `9 ^ (m - 1) ≤ n`, round `m ≥ 1` has scalar
cost at most `13 * Real.sqrt n`. -/
theorem paper_query_cost_le_sqrt (C : ℕ → ℝ) (hC : PaperCostLaw C) (m : ℕ)
    (hm : 1 ≤ m) (n : ℝ) (_hn : 0 < n) (hschedule : 9 ^ (m - 1) ≤ n) :
    C m ≤ 13 * Real.sqrt n := by
  have hcost := paper_cost_le C hC m hm
  have h3le : (3 : ℝ) ^ (m - 1) ≤ Real.sqrt n := by
    have h9 : (9 : ℝ) ^ (m - 1) = ((3 : ℝ) ^ (m - 1)) ^ 2 := by
      calc (9 : ℝ) ^ (m - 1) = (3 ^ 2) ^ (m - 1) := by
            rw [show (9 : ℝ) = 3 ^ 2 by norm_num]
        _ = 3 ^ (2 * (m - 1)) := (pow_mul (3 : ℝ) 2 (m - 1)).symm
        _ = 3 ^ ((m - 1) * 2) := by rw [Nat.mul_comm]
        _ = ((3 : ℝ) ^ (m - 1)) ^ 2 := pow_mul (3 : ℝ) (m - 1) 2
    calc (3 : ℝ) ^ (m - 1)
        = Real.sqrt (((3 : ℝ) ^ (m - 1)) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ = Real.sqrt (9 ^ (m - 1)) := by rw [h9]
      _ ≤ Real.sqrt n := Real.sqrt_le_sqrt hschedule
  calc C m ≤ 13 * 3 ^ (m - 1) := hcost
    _ ≤ 13 * Real.sqrt n := mul_le_mul_of_nonneg_left h3le (by norm_num)

/-- The sum of the first `n` powers of three is at most `3 ^ n / 2`. -/
theorem geom_sum_three_le (n : ℕ) :
    ∑ k ∈ Finset.range n, (3 : ℝ) ^ k ≤ 3 ^ n / 2 := by
  rw [geom_sum_eq (by norm_num : (3 : ℝ) ≠ 1) n]
  have h : (0 : ℝ) < 3 ^ n := pow_pos (by norm_num) n
  rw [show (3 : ℝ) - 1 = 2 by norm_num]
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  nlinarith

/-- For `n ≥ 1`, the natural logarithm is at most `2 * Real.sqrt n`. -/
theorem log_le_two_sqrt (n : ℝ) (hn : 1 ≤ n) : Real.log n ≤ 2 * Real.sqrt n := by
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hlog : Real.log n = 2 * Real.log (Real.sqrt n) := by
    rw [Real.log_sqrt hn0]; ring
  have hpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
  have h1 : Real.log (Real.sqrt n) ≤ Real.sqrt n - 1 := Real.log_le_sub_one_of_pos hpos
  have h2 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hn
  rw [hlog]
  linarith

/-- The scalar total `1000 * ∑ m < M, C (m + 1) + 1000 * V * Real.log n`, combining repeated
round costs with a logarithmic verification term. -/
def totalCost (C : ℕ → ℝ) (V : ℝ) (M : ℕ) (n : ℝ) : ℝ :=
  1000 * (∑ m ∈ Finset.range M, C (m + 1)) + 1000 * V * Real.log n

/-- Under `PaperCostLaw`, the schedule condition, and the stated nonnegativity and logarithm
bounds, `totalCost C V M n` is at most `(19500 + 2000 * V) * Real.sqrt n`. This bounds the
specified scalar total used in [HoyerMoscaDeWolf2003]. -/
theorem total_cost_le_sqrt (C : ℕ → ℝ) (hC : PaperCostLaw C) (V : ℝ) (hV : 0 ≤ V)
    (M : ℕ) (hM : 1 ≤ M) (n : ℝ) (_hn : 1 ≤ n)
    (hschedule : 9 ^ (M - 1) ≤ n) (hlog : Real.log n ≤ 2 * Real.sqrt n) :
    totalCost C V M n ≤ (19500 + 2000 * V) * Real.sqrt n := by
  unfold totalCost
  have hterm : ∀ m ∈ Finset.range M, C (m + 1) ≤ 13 * 3 ^ m := by
    intro m _
    have h := paper_cost_le C hC (m + 1) (by omega)
    rwa [show m + 1 - 1 = m by omega] at h
  have hsum : ∑ m ∈ Finset.range M, C (m + 1) ≤ 13 * (3 ^ M / 2) := by
    calc ∑ m ∈ Finset.range M, C (m + 1) ≤ ∑ m ∈ Finset.range M, 13 * 3 ^ m :=
          Finset.sum_le_sum hterm
      _ = 13 * ∑ m ∈ Finset.range M, 3 ^ m := by rw [Finset.mul_sum]
      _ ≤ 13 * (3 ^ M / 2) :=
          mul_le_mul_of_nonneg_left (geom_sum_three_le M) (by norm_num)
  have hsqrt_nn : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg n
  have h3M : (3 : ℝ) ^ M ≤ 3 * Real.sqrt n := by
    have h3 : (3 : ℝ) ^ (M - 1) ≤ Real.sqrt n := by
      have h9 : (9 : ℝ) ^ (M - 1) = ((3 : ℝ) ^ (M - 1)) ^ 2 := by
        calc (9 : ℝ) ^ (M - 1) = (3 ^ 2) ^ (M - 1) := by
              rw [show (9 : ℝ) = 3 ^ 2 by norm_num]
          _ = 3 ^ (2 * (M - 1)) := (pow_mul (3 : ℝ) 2 (M - 1)).symm
          _ = 3 ^ ((M - 1) * 2) := by rw [Nat.mul_comm]
          _ = ((3 : ℝ) ^ (M - 1)) ^ 2 := pow_mul (3 : ℝ) (M - 1) 2
      calc (3 : ℝ) ^ (M - 1)
          = Real.sqrt (((3 : ℝ) ^ (M - 1)) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ = Real.sqrt (9 ^ (M - 1)) := by rw [h9]
        _ ≤ Real.sqrt n := Real.sqrt_le_sqrt hschedule
    calc (3 : ℝ) ^ M = 3 ^ ((M - 1) + 1) := by rw [Nat.sub_add_cancel hM]
      _ = 3 * 3 ^ (M - 1) := by rw [pow_succ']
      _ ≤ 3 * Real.sqrt n := mul_le_mul_of_nonneg_left h3 (by norm_num)
  have hSum : ∑ m ∈ Finset.range M, C (m + 1) ≤ 13 * (3 * Real.sqrt n / 2) := by
    calc ∑ m ∈ Finset.range M, C (m + 1) ≤ 13 * (3 ^ M / 2) := hsum
      _ ≤ 13 * (3 * Real.sqrt n / 2) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          nlinarith [h3M]
  have hlogterm : 1000 * V * Real.log n ≤ 1000 * V * (2 * Real.sqrt n) := by
    apply mul_le_mul_of_nonneg_left hlog
    positivity
  calc 1000 * (∑ m ∈ Finset.range M, C (m + 1)) + 1000 * V * Real.log n
      ≤ 1000 * (13 * (3 * Real.sqrt n / 2)) + 1000 * V * (2 * Real.sqrt n) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hSum (by norm_num)
        · exact hlogterm
    _ ≤ (19500 + 2000 * V) * Real.sqrt n := by
        nlinarith [hsqrt_nn, hV, mul_nonneg hV hsqrt_nn]

/-- For `0 < p ≤ 1`, the failure expression `(1 - p) ^ r` tends to zero as the repetition count
tends to infinity. -/
theorem repeat_failure_tendsto_zero (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    Filter.Tendsto (fun r : ℕ => (1 - p) ^ r) Filter.atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)

/-- For `1/576 ≤ p ≤ 1`, the scalar success expression `1 - (1 - p) ^ 1000` is at least one
half. This gives the constant-repetition estimate used in [HoyerMoscaDeWolf2003]. -/
theorem thousand_repeat_success_ge (p : ℝ) (hp : (1 / 576 : ℝ) ≤ p) (hp1 : p ≤ 1) :
    (1 / 2 : ℝ) ≤ 1 - (1 - p) ^ 1000 := by
  have hnn : (0 : ℝ) ≤ 1 - p := by linarith
  have hbase : 1 - p ≤ 575 / 576 := by linarith
  have hmono : (1 - p) ^ 1000 ≤ (575 / 576 : ℝ) ^ 1000 :=
    pow_le_pow_left₀ hnn hbase 1000
  have hbern : (1 : ℝ) + (1000 : ℝ) * (1 / 575) ≤ (1 + 1 / 575) ^ 1000 :=
    one_add_mul_le_pow (by norm_num) 1000
  have hgt : (2 : ℝ) < (576 / 575 : ℝ) ^ 1000 := by
    have hsmall : (2 : ℝ) < 1 + (1000 : ℝ) * (1 / 575) := by norm_num
    have heq : (1 + 1 / 575 : ℝ) = 576 / 575 := by norm_num
    rw [heq] at hbern
    exact lt_of_lt_of_le hsmall hbern
  have hinv : 1 / (576 / 575 : ℝ) ^ 1000 < 1 / 2 :=
    one_div_lt_one_div_of_lt (by norm_num) hgt
  have heq : (575 / 576 : ℝ) ^ 1000 = 1 / (576 / 575 : ℝ) ^ 1000 := by
    rw [one_div, ← inv_pow]
    congr 1
    norm_num
  have hfin : (1 - p) ^ 1000 ≤ 1 / 2 := by
    calc (1 - p) ^ 1000 ≤ (575 / 576 : ℝ) ^ 1000 := hmono
      _ = 1 / (576 / 575 : ℝ) ^ 1000 := heq
      _ ≤ 1 / 2 := le_of_lt hinv
  have hstep := sub_le_sub_left hfin 1
  norm_num at hstep ⊢
  exact hstep

end Qatlib.Papers.BndErrSearch03.MainResults.SearchRepetitionCost
