/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section


/-! # The genuine search-cost sum from Lemma 4.1

Fixed source: Childs--Kothari, arXiv1011.1443v2, display (1).
This proves the entire numerical sum bound by telescoping square roots.
It supplies no Grover/counting program or source-query composition theorem.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.MinorClosed10.MainResults.SearchSum

/-- The reciprocal square-root term is bounded by twice the consecutive root increment. -/
theorem rootStep (k : ℕ) :
    1/Real.sqrt ((k+1 : ℕ) : ℝ) ≤
      2*(Real.sqrt ((k+1 : ℕ) : ℝ)-Real.sqrt (k : ℝ)) := by
  have hn : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hp : (0 : ℝ) < ((k+1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos k)
  have hs := Real.sqrt_pos.mpr hp
  have ht := Real.sq_sqrt hn
  have hu := Real.sq_sqrt hp.le
  apply (div_le_iff₀ hs).mpr
  have hd := sq_nonneg (Real.sqrt ((k+1 : ℕ) : ℝ)-Real.sqrt (k : ℝ))
  push_cast at *
  nlinarith

/-- The entire finite reciprocal square-root sum is at most twice the final root. -/
theorem rootSum (K : ℕ) :
    ∑ j ∈ Finset.range K, 1/Real.sqrt ((j+1 : ℕ) : ℝ) ≤ 2*Real.sqrt (K : ℝ) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have hs := rootStep K
    linarith

/-- The genuine marked-search cost sum in increasing denominator order obeys the printed two-root bound. -/
theorem scaledSum (N K : ℕ) :
    ∑ j ∈ Finset.range K, Real.sqrt ((N : ℝ)/((j+1 : ℕ) : ℝ)) ≤
      2*Real.sqrt ((N : ℝ)*(K : ℝ)) := by
  have he : ∀ j : ℕ, Real.sqrt ((N : ℝ)/((j+1 : ℕ) : ℝ)) =
      Real.sqrt (N : ℝ)*(1/Real.sqrt ((j+1 : ℕ) : ℝ)) := by
    intro j
    rw [Real.sqrt_div (Nat.cast_nonneg N)]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum, Real.sqrt_mul (Nat.cast_nonneg N)]
  have h := mul_le_mul_of_nonneg_left (rootSum K) (Real.sqrt_nonneg (N : ℝ))
  nlinarith

end Qatlib.Papers.MinorClosed10.MainResults.SearchSum
