/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.NonlinearDE20.AffineLift.AffineHomogenization
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

/-!
# Term count for the normalization square root

The supplement of [LloydEtAl2020] augments the rescaled state by `sqrt (1 - y)` with
`y = x̃†x̃` and truncates the Taylor series of `(1 - y)^(-1/2)`, whose coefficients are the central
binomial coefficients divided by powers of four. The printed argument only says that the series
converges exponentially and that the number of terms grows like `log (1 / ε)`.

This module isolates the part of that statement that does not need the identity between the
binomial series and the square root: on `[0, 1/2]` the `K`-th geometric tail `2 * y^K` is at most
`ε` once `K` is the ceiling of `logb 2 (2 / ε)`, and that ceiling is at most
`2 * logb 2 (1 / ε) + 2`. The exponent is uniform in `y`.

## Boundary

The degree bound `K ≤ C * logb 2 (1 / ε) + C` is not satisfiable for every `ε > 0`: a positive
constant makes the right-hand side negative once `ε > 2`, while `K` is a natural number. The
statement `literal_taylor_degree_statement_false` records that defect at `ε = 4`, and the positive
result below carries the explicit small-tolerance hypothesis `ε ≤ 1`, which is the regime in
which the truncation is used.

The identification of the truncated polynomial with the central-binomial series, and hence the
remainder bound for the square root itself, is not proved here; it needs the half-integer
binomial coefficient identity together with the binomial series of `(1 - y)^(-1/2)`.

## Main statements

* `literal_taylor_degree_statement_false`: the printed degree bound is unsatisfiable as stated.
* `geometric_tail_budget`: the ceiling of `logb 2 (2 / ε)` terms make the geometric tail on
  `[0, 1/2]` at most `ε`.
* `taylor_degree_small_tolerance`: for `0 < ε ≤ 1` the term count is at most
  `2 * logb 2 (1 / ε) + 2` and the geometric tail is at most `ε`.

## References

* [Lloyd et al., 2020][LloydEtAl2020]
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.NonlinearDE20.ErrorAnalysis.Taylor

/-- The printed Taylor degree bound for the normalization square root is unsatisfiable as stated:
at `ε = 4` the right-hand side `C * logb 2 (1 / ε) + C` equals `-C`, which is negative for every
positive constant, while the number of terms is a natural number. -/
theorem literal_taylor_degree_statement_false :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∃ K : ℕ,
      (K : ℝ) ≤ C * Real.logb 2 (1 / ε) + C ∧
        (∀ y : ℝ, 0 ≤ y → y ≤ 1 / 2 →
          |(1 - y) ^ (-(1 / 2) : ℝ) -
            ∑ k ∈ Finset.range K, (Nat.choose (2 * k) k : ℝ) * (y / 4) ^ k| ≤ ε) := by
  rintro ⟨C, hC, h⟩
  obtain ⟨K, hK, _⟩ := h 4 (by norm_num)
  have h4 : Real.logb 2 (1 / (4 : ℝ)) = -2 := by
    have hlog4 : Real.logb 2 (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num,
        Real.logb_mul (b := 2) (by norm_num) (by norm_num),
        Real.logb_self_eq_one (b := 2) (by norm_num)]
      norm_num
    rw [Real.logb_div (b := 2) (by norm_num) (by norm_num), Real.logb_one, hlog4]
    norm_num
  rw [h4] at hK
  have hneg : C * (-2) + C < 0 := by nlinarith
  have hnonneg : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  linarith

/-- For positive tolerance, `Nat.ceil (logb 2 (2 / ε))` terms make the geometric tail `2 * y^K`
at most `ε` for every `0 ≤ y ≤ 1/2`. -/
theorem geometric_tail_budget {ε : ℝ} (hε : 0 < ε) :
    ∀ y : ℝ, 0 ≤ y → y ≤ 1 / 2 →
      2 * y ^ Nat.ceil (Real.logb 2 (2 / ε)) ≤ ε := by
  have hxb : (0 : ℝ) < 2 / ε := by positivity
  have hKge : Real.logb 2 (2 / ε) ≤ ((Nat.ceil (Real.logb 2 (2 / ε)) : ℕ) : ℝ) := Nat.le_ceil _
  have hbase : (2 : ℝ) ^ Real.logb 2 (2 / ε) = 2 / ε :=
    Real.rpow_logb (by norm_num) (by norm_num) hxb
  have hmono : (2 : ℝ) ^ Real.logb 2 (2 / ε) ≤
      (2 : ℝ) ^ ((Nat.ceil (Real.logb 2 (2 / ε)) : ℕ) : ℝ) :=
    (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr hKge
  rw [hbase, Real.rpow_natCast] at hmono
  have hle : 2 * ((1 / 2 : ℝ) ^ Nat.ceil (Real.logb 2 (2 / ε))) ≤ ε := by
    have h2 : 2 ≤ ε * (2 : ℝ) ^ Nat.ceil (Real.logb 2 (2 / ε)) := by
      have h := mul_le_mul_of_nonneg_left hmono hε.le
      field_simp at h
      linarith
    have hinv : ((1 / 2 : ℝ) ^ Nat.ceil (Real.logb 2 (2 / ε))) =
        ((2 : ℝ) ^ Nat.ceil (Real.logb 2 (2 / ε)))⁻¹ := by
      rw [div_pow, one_pow, one_div]
    rw [hinv, ← div_eq_mul_inv]
    rw [div_le_iff₀ (by positivity)]
    exact h2
  intro y hy0 hy
  have hyK : y ^ Nat.ceil (Real.logb 2 (2 / ε)) ≤
      (1 / 2 : ℝ) ^ Nat.ceil (Real.logb 2 (2 / ε)) := pow_le_pow_left₀ hy0 hy _
  linarith

/-- For `0 < ε ≤ 1` there are at most `2 * logb 2 (1 / ε) + 2` terms in the normalization Taylor
truncation whose geometric tail on `[0, 1/2]` is at most `ε`; this is the `log (1 / ε)` degree
count of [LloydEtAl2020] separated from the square-root remainder estimate. -/
theorem taylor_degree_small_tolerance :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ K : ℕ,
      (K : ℝ) ≤ C * Real.logb 2 (1 / ε) + C ∧
        ∀ y : ℝ, 0 ≤ y → y ≤ 1 / 2 → 2 * y ^ K ≤ ε := by
  refine ⟨2, by norm_num, ?_⟩
  intro ε hε hε1
  refine ⟨Nat.ceil (Real.logb 2 (2 / ε)), ?_, geometric_tail_budget hε⟩
  have hMpos : 0 ≤ Real.logb 2 (2 / ε) := by
    apply Real.logb_nonneg (b := 2) (by norm_num)
    rw [le_div_iff₀ hε]
    nlinarith
  have hKlt : ((Nat.ceil (Real.logb 2 (2 / ε)) : ℕ) : ℝ) < Real.logb 2 (2 / ε) + 1 :=
    Nat.ceil_lt_add_one hMpos
  have hsplit : Real.logb 2 (2 / ε) = 1 + Real.logb 2 (1 / ε) := by
    rw [show (2 : ℝ) / ε = 2 * (1 / ε) by field_simp]
    rw [Real.logb_mul (b := 2) (by norm_num) (by positivity),
      Real.logb_self_eq_one (b := 2) (by norm_num)]
  have hL : 0 ≤ Real.logb 2 (1 / ε) := by
    apply Real.logb_nonneg (b := 2) (by norm_num)
    rw [one_div, one_le_inv₀ hε]
    exact hε1
  rw [hsplit] at hKlt ⊢
  linarith

end Qatlib.Papers.NonlinearDE20.ErrorAnalysis.Taylor
