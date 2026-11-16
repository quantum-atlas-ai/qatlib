/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section


/-! Scalar counterexamples to source runtime and free failure-bound contracts. -/
set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SDPBrandao16.MainResults.ContractRefute

/-- A free nonnegative runtime need not satisfy the source Corollary 5 upper bound. -/
theorem corollary5_contract_false :
    ¬ (∀ n m s R δ T : ℝ,
      1 ≤ n → 1 ≤ m → 1 ≤ s → 1 ≤ R → 0 < δ → δ ≤ 1 →
      0 ≤ T → T ≤ (Real.sqrt n * Real.sqrt m * s ^ 2 * R ^ 32) / δ ^ 18) := by
  intro h
  have hh := h 1 1 1 1 1 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hh

/-- Zero primitive costs and a positive free runtime refute Theorems 4 and 14. -/
theorem theorem4_runtime_contract_false :
    ¬ (∀ R δ Gh GM TMeas T : ℝ,
      1 ≤ R → 0 < δ → δ ≤ 1 → 0 ≤ Gh → 0 ≤ GM → 0 ≤ TMeas → 0 ≤ T →
      T ≤ (R ^ 21 / δ ^ 11) * (Gh * GM) + (R ^ 13 / δ ^ 5) * TMeas) := by
  intro h
  have hh := h 1 1 0 0 0 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hh

/-- A merely nonnegative free failure scalar is not bounded by the source expression. -/
theorem theorem4_failure_contract_false :
    ¬ (∀ R δ n m ξ pFail : ℝ,
      1 ≤ R → 0 < δ → δ ≤ 1 → 1 ≤ n → 1 ≤ m → 0 < ξ → 0 ≤ pFail →
      pFail ≤ (R / δ) ^ 18 * (n * m) ^ 10 *
        Real.exp (-(Real.log (n * m)) ^ ξ)) := by
  intro h
  have hh := h 1 1 1 1 1 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hh

/-- A positive workspace coefficient multiplying log of a half has a negative budget. -/
theorem negative_log_workspace (K : ℝ) (hK : 0 < K) (workspace : ℕ) :
    ¬ (workspace : ℝ) ≤ K * Real.log ((1 : ℝ) / 2) := by
  have hlog : Real.log ((1 : ℝ) / 2) < 0 :=
    Real.log_neg (by norm_num) (by norm_num)
  have hneg := mul_neg_of_pos_of_neg hK hlog
  have hnonneg : (0 : ℝ) ≤ (workspace : ℝ) := Nat.cast_nonneg workspace
  linarith

end Qatlib.Papers.SDPBrandao16.MainResults.ContractRefute
