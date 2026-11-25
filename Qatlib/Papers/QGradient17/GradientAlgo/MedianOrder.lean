/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GradientOracle.ReadoutTools.AlmostAffineGradient
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

/-!
# Query order of the coordinate median

Theorem 21 of Gilyén, Arunachalam and Wiebe (arXiv:1711.00465v3) uses a
logarithmic number of fresh phase queries. Bound the exact repetition count
in the pinned implementation using the ceiling logarithms of the dimension
and inverse failure tolerance.
-/

set_option autoImplicit false

open Qatlib.Concepts.GradientOracle.ReadoutTools

namespace Qatlib.Papers.QGradient17.GradientAlgo

/-- Bound the odd number of queries in the coordinate median using integer ceiling logarithms. -/
theorem median_queries_nat_le (d : ℕ) (δ : ℚ) :
    2 * gradientMedianRepetitions d δ + 1 ≤
      202 * (Nat.clog 2 (max 1 d) + Nat.clog 2 (max 1 (Nat.ceil (1 / δ))) + 1) := by
  unfold gradientMedianRepetitions
  omega

private theorem clog_two_cast_lt {n : ℕ} (hn : 0 < n) :
    (Nat.clog 2 n : ℝ) < Real.logb 2 (n : ℝ) + 1 := by
  rw [← Real.natCeil_logb_natCast]
  exact Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num)
    (Nat.one_le_cast.mpr hn))

/-- Theorem 21's exact median query count is bounded by the sum of the base-two
logs of the dimension and inverse failure tolerance, with explicit constants. -/
theorem median_queries_log_le (d : ℕ) {δ : ℚ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ((2 * gradientMedianRepetitions d δ + 1 : ℕ) : ℝ) ≤
      404 * (Real.logb 2 ((d : ℝ) + 1) + Real.logb 2 (1 / (δ : ℝ)) + 2) := by
  have hδr : 0 < (δ : ℝ) := by exact_mod_cast hδ
  have hδr1 : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have hinv : (1 : ℝ) ≤ 1 / (δ : ℝ) := (le_div_iff₀ hδr).2 (by simpa using hδr1)
  have hdim : ((max 1 d : ℕ) : ℝ) ≤ (d : ℝ) + 1 := by
    exact_mod_cast (max_le (Nat.succ_le_succ (Nat.zero_le d)) (Nat.le_add_right d 1))
  have hceilQ : ((Nat.ceil (1 / δ) : ℕ) : ℚ) < 1 / δ + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hceil : ((Nat.ceil (1 / δ) : ℕ) : ℝ) < 1 / (δ : ℝ) + 1 := by
    exact_mod_cast hceilQ
  have hconf : ((max 1 (Nat.ceil (1 / δ)) : ℕ) : ℝ) ≤ 2 * (1 / (δ : ℝ)) := by
    push_cast
    exact max_le (by linarith) (by linarith)
  have hd := (clog_two_cast_lt (lt_of_lt_of_le (by decide : 0 < 1) (le_max_left 1 d))).trans_le
    (add_le_add (Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hdim)
      (le_refl (1 : ℝ)))
  have hfail := (clog_two_cast_lt (lt_of_lt_of_le (by decide : 0 < 1)
    (le_max_left 1 (Nat.ceil (1 / δ))))).trans_le
    (add_le_add (Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hconf)
      (le_refl (1 : ℝ)))
  rw [Real.logb_mul (by norm_num) (by positivity),
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at hfail
  have hledger := median_queries_nat_le d δ
  have hcast := (Nat.cast_le (α := ℝ)).2 hledger
  push_cast at hcast
  have hlogd : 0 ≤ Real.logb 2 ((d : ℝ) + 1) :=
    Real.logb_nonneg (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) d])
  have hlogδ : 0 ≤ Real.logb 2 (1 / (δ : ℝ)) := Real.logb_nonneg (by norm_num) hinv
  push_cast
  linarith

end Qatlib.Papers.QGradient17.GradientAlgo
