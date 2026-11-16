/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BoolEquation17.MainResults.Support
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section


/-! # A uniform bound on the Boolean-system arithmetic index cost. -/
set_option autoImplicit false
namespace Qatlib.Papers.BoolEquation17.MainResults
/-- The ceiling binary logarithm has a uniform bound by twice the real binary logarithm for integers at least two. -/
theorem clog_uniform (m : ℕ) (hm : 2 ≤ m) :
    (Nat.clog 2 m : ℝ) ≤ (2 / Real.log 2) * Real.log (m : ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlogm : Real.log 2 ≤ Real.log (m : ℝ) := Real.log_le_log (by norm_num) hmR
  have hnonneg : 0 ≤ Real.logb 2 (m : ℝ) := by
    rw [Real.logb]
    exact div_nonneg (le_trans hlog2.le hlogm) hlog2.le
  have hceil : (Nat.clog 2 m : ℝ) ≤ Real.log (m : ℝ) / Real.log 2 + 1 := by
    rw [← Real.natCeil_logb_natCast]
    simpa only [Real.logb, Nat.cast_ofNat] using (Nat.ceil_lt_add_one hnonneg).le
  have hratio : 1 ≤ Real.log (m : ℝ) / Real.log 2 := by
    rw [le_div_iff₀ hlog2]
    simpa using hlogm
  calc (Nat.clog 2 m : ℝ) ≤ 2 * (Real.log (m : ℝ) / Real.log 2) := by linarith
    _ = (2 / Real.log 2) * Real.log (m : ℝ) := by ring

/-- The arithmetic index-cost expression appearing in the legacy Lemma 3.10. -/
def macaulayQueryCost (n D r : ℕ) : ℕ := n * Nat.clog 2 (D + 2) + Nat.clog 2 (r + 2)

/-- A single explicit constant controls the query-cost expression for all dimensions and degrees. -/
theorem query_uniform (n D r : ℕ) :
    (macaulayQueryCost n D r : ℝ) ≤
      (2 / Real.log 2) * ((n : ℝ) * Real.log (D + 2) + Real.log (r + 2)) := by
  have hD := clog_uniform (D + 2) (by omega)
  have hr := clog_uniform (r + 2) (by omega)
  have hsum := add_le_add (mul_le_mul_of_nonneg_left hD (Nat.cast_nonneg (α := ℝ) n)) hr
  dsimp [macaulayQueryCost]
  push_cast at hsum ⊢
  nlinarith

/-- The legacy Lemma 3.10 arithmetic inequality follows from a dimension-independent explicit constant. -/
theorem lemma_3_10 (n D r : ℕ) :
    IsBigO (macaulayQueryCost n D r : ℝ)
      ((n : ℝ) * Real.log (D + 2) + Real.log (r + 2)) := by
  exact ⟨2 / Real.log 2, by positivity, query_uniform n D r⟩

end Qatlib.Papers.BoolEquation17.MainResults
