/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Taylor truncation order of Theorem 14

Theorem 14 of [GilyenArunachalamWiebe2019] (arXiv:1711.00465v3, §4.2, p.18)
truncates the Taylor series of the time-evolution operator and charges a single
error term of `1/M!` for a degree-`M` truncation. Equations (11)-(13) of the
source then choose `M` from the tolerance: for `ε ∈ (0, 1/3)` any
`M ≥ 2 ln(1/ε) / ln ln(1/ε)` satisfies `1/M! ≤ (e/M)^M ≤ ε`.

This file isolates that analytic estimate. `inv_factorial_le_exp_div_pow` is the
elementary Stirling lower bound `(n/e)^n ≤ n!` in the reciprocal form
`1/n! ≤ (e/n)^n`. `exp_div_pow_le_of_log_bound` converts the source's
logarithmic threshold on `M` into `(e/M)^M ≤ ε`. Their composition
`inv_factorial_le_of_log_truncation` is the resulting order bound.

The file says nothing about the LCU block encoding that performs the truncated
series, about the accuracy of the truncated exponential at a finite time, or
about the regime `ε ≥ 1/3`: the first two belong to the circuit layer, and the
third is outside the source's hypothesis.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QGradient17.ReadoutTools.Algorithm

/-- The reciprocal Stirling lower bound `(n/e)^n ≤ n!` in the form used for the Taylor truncation
error: `1/n! ≤ (e/n)^n`. -/
theorem inv_factorial_le_exp_div_pow (n : ℕ) (hn : 1 ≤ n) :
    1 / (n.factorial : ℝ) ≤ (Real.exp 1 / n) ^ n := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hbase : (0 : ℝ) < (n : ℝ) / Real.exp 1 :=
    div_pos hnr (Real.exp_pos 1)
  have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * n) := by
    have hπ : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hnn : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hp : (1 : ℝ) ^ 2 ≤ 2 * Real.pi * n := by nlinarith
    have h := Real.sqrt_le_sqrt hp
    simpa using h
  have hf : ((n : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) := by
    have h0 := Stirling.le_factorial_stirling n
    have h1 : ((n : ℝ) / Real.exp 1) ^ n ≤
        Real.sqrt (2 * Real.pi * n) * ((n : ℝ) / Real.exp 1) ^ n := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hsqrt (pow_nonneg hbase.le n)
    exact h1.trans h0
  have hpos : 0 < ((n : ℝ) / Real.exp 1) ^ n := pow_pos hbase n
  have hmain : 1 / ((n : ℝ) / Real.exp 1) ^ n = (Real.exp 1 / n) ^ n := by
    rw [one_div, ← inv_pow, inv_div]
  rw [← hmain]
  exact one_div_le_one_div_of_le hpos hf

/-- The logarithm of `e/M` is `1 - log M`. -/
private theorem log_exp_div (M : ℕ) (hM : (0 : ℝ) < M) :
    Real.log (Real.exp 1 / M) = 1 - Real.log M := by
  rw [Real.log_div (Real.exp_pos 1).ne' hM.ne', Real.log_exp]

/-- The source's threshold `2 ln(1/ε) / ln ln(1/ε) ≤ M` forces `ln(1/ε) ≤ M (ln M - 1)`, which is
the logarithmic form of `(e/M)^M ≤ ε`. -/
private theorem log_bound_of_threshold {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀3 : ε₀ < 1 / 3)
    {M : ℕ} (hM : 2 * Real.log (1 / ε₀) / Real.log (Real.log (1 / ε₀)) ≤ M) :
    Real.log (1 / ε₀) ≤ (M : ℝ) * (Real.log M - 1) := by
  set L := Real.log (1 / ε₀) with hL
  set L' := Real.log L with hL'
  have hinv : (3 : ℝ) < 1 / ε₀ := by
    have := one_div_lt_one_div_of_lt hε₀ hε₀3
    norm_num at this ⊢
    exact this
  have hL1 : 1 < L := by
    have h3 : Real.exp 1 < 1 / ε₀ := Real.exp_one_lt_three.trans hinv
    have := Real.log_lt_log (Real.exp_pos 1) h3
    rwa [Real.log_exp] at this
  have hL'pos : 0 < L' := Real.log_pos hL1
  have hthr_pos : (0 : ℝ) < 2 * L / L' := by
    have hLpos : 0 < L := by linarith
    positivity
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le hthr_pos hM
  have hlogM : Real.log (2 * L / L') ≤ Real.log M := Real.log_le_log hthr_pos hM
  have hlog_split : Real.log (2 * L / L') = Real.log 2 + L' - Real.log L' := by
    rw [Real.log_div (by positivity) (ne_of_gt hL'pos),
      Real.log_mul (by norm_num) (ne_of_gt (by linarith : (0 : ℝ) < L)), hL']
  have hlogL' : Real.log L' ≤ L' / 2 - (1 - Real.log 2) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < L' / 2 by positivity)
    have hsplit : Real.log L' = Real.log 2 + Real.log (L' / 2) := by
      rw [← Real.log_mul (by norm_num) (by positivity), show 2 * (L' / 2) = L' by ring]
    linarith
  have ht_pos : 0 < Real.log 2 + L' - Real.log L' - 1 := by
    have h := Real.log_le_sub_one_of_pos hL'pos
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have ht_key : L ≤ 2 * L / L' * (Real.log 2 + L' - Real.log L' - 1) := by
    have hLpos : 0 < L := by linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hL'pos]
    nlinarith [hlogL']
  have ht_le : Real.log 2 + L' - Real.log L' - 1 ≤ Real.log M - 1 := by
    linarith
  calc L ≤ 2 * L / L' * (Real.log 2 + L' - Real.log L' - 1) := ht_key
    _ ≤ 2 * L / L' * (Real.log M - 1) :=
          mul_le_mul_of_nonneg_left ht_le hthr_pos.le
    _ ≤ (M : ℝ) * (Real.log M - 1) :=
          mul_le_mul_of_nonneg_right hM (by linarith)

/-- The `(e/M)^M ≤ ε` half of the truncation estimate of Theorem 14: the source's logarithmic
threshold on the truncation order `M` makes the degree-`M` Taylor remainder budget `1/M!` at most
`(e/M)^M ≤ ε`. -/
theorem exp_div_pow_le_of_log_bound {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀3 : ε₀ < 1 / 3)
    {M : ℕ} (hM : 2 * Real.log (1 / ε₀) / Real.log (Real.log (1 / ε₀)) ≤ M) :
    (Real.exp 1 / M) ^ M ≤ ε₀ := by
  have hinv3 : (3 : ℝ) < 1 / ε₀ := by
    have := one_div_lt_one_div_of_lt hε₀ hε₀3
    norm_num at this ⊢
    exact this
  have hL1 : 1 < Real.log (1 / ε₀) := by
    have h3 : Real.exp 1 < 1 / ε₀ := Real.exp_one_lt_three.trans hinv3
    have := Real.log_lt_log (Real.exp_pos 1) h3
    rwa [Real.log_exp] at this
  have hLpos : (0 : ℝ) < Real.log (1 / ε₀) := lt_trans zero_lt_one hL1
  have hMpos : (0 : ℝ) < M := by
    have hthr : (0 : ℝ) < 2 * Real.log (1 / ε₀) / Real.log (Real.log (1 / ε₀)) := by
      have := Real.log_pos hL1
      positivity
    exact lt_of_lt_of_le hthr hM
  have hlogε : Real.log ε₀ = -Real.log (1 / ε₀) := by
    rw [one_div, Real.log_inv, neg_neg]
  have hkey : (M : ℝ) * Real.log (Real.exp 1 / M) ≤ Real.log ε₀ := by
    rw [log_exp_div M hMpos, hlogε]
    have := log_bound_of_threshold hε₀ hε₀3 hM
    nlinarith
  have hpow : (Real.exp 1 / M) ^ M =
      Real.exp ((M : ℝ) * Real.log (Real.exp 1 / M)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
  rw [hpow, ← Real.exp_log hε₀]
  exact Real.exp_le_exp.mpr hkey

/-- Theorem 14's truncation estimate (arXiv:1711.00465v3, §4.2, Eqs. (11)-(13)): for
`ε₀ ∈ (0, 1/3)` and a truncation order `M ≥ 2 ln(1/ε₀) / ln ln(1/ε₀)`, the degree-`M` Taylor
remainder budget `1/M!` is at most `ε₀`. -/
theorem inv_factorial_le_of_log_truncation (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀3 : ε₀ < 1 / 3)
    (M : ℕ) (hM2 : 2 ≤ M)
    (hM : 2 * Real.log (1 / ε₀) / Real.log (Real.log (1 / ε₀)) ≤ M) :
    1 / (M.factorial : ℝ) ≤ ε₀ := by
  have hM1 : 1 ≤ M := le_trans (by norm_num) hM2
  exact (inv_factorial_le_exp_div_pow M hM1).trans (exp_div_pow_le_of_log_bound hε₀ hε₀3 hM)

end Qatlib.Papers.QGradient17.ReadoutTools.Algorithm
