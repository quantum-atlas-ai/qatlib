/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.BndErrSearch03.MainResults.AndOrTreeQueryCost

def andOrCost (c N : ℝ) : ℕ → ℝ
  | 0 => Real.sqrt N
  | d + 1 => c * andOrCost c N d

theorem andOr_cost_closed (c N : ℝ) (d : ℕ) :
    andOrCost c N d = c ^ d * Real.sqrt N := by
  induction d with
  | zero => simp [andOrCost]
  | succ d ih =>
    show c * andOrCost c N d = c ^ (d + 1) * Real.sqrt N
    rw [ih, pow_succ]
    ring

theorem andOr_cost_depth (c N : ℝ) (d : ℕ) (_hd : 1 ≤ d) :
    andOrCost c N (d - 1) = c ^ (d - 1) * Real.sqrt N :=
  andOr_cost_closed c N (d - 1)

theorem andOr_cost_le_const_mul_sqrt (c N : ℝ) (_hc : 0 ≤ c) (d : ℕ) (hd : 1 ≤ d) :
    andOrCost c N (d - 1) ≤ c ^ (d - 1) * Real.sqrt N := by
  rw [andOr_cost_depth c N d hd]

theorem andOr_cost_le_log_pow (c N : ℝ) (hc : 0 ≤ c) (_hN : 1 ≤ N)
    (hclog : c ≤ Real.log N) (d : ℕ) (hd : 1 ≤ d) :
    andOrCost c N (d - 1) ≤ (Real.log N) ^ (d - 1) * Real.sqrt N := by
  rw [andOr_cost_depth c N d hd]
  have hpow : c ^ (d - 1) ≤ (Real.log N) ^ (d - 1) :=
    pow_le_pow_left₀ hc hclog (d - 1)
  exact mul_le_mul_of_nonneg_right hpow (Real.sqrt_nonneg N)

theorem andOr_cost_uniform (c : ℝ) (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, 0 ≤ N →
      andOrCost c N (d - 1) ≤ C * Real.sqrt N := by
  refine ⟨|c| ^ (d - 1), pow_nonneg (abs_nonneg c) _, ?_⟩
  intro N _hN
  rw [andOr_cost_depth c N d hd]
  have hcle : c ^ (d - 1) ≤ |c| ^ (d - 1) := by
    calc c ^ (d - 1) ≤ |c ^ (d - 1)| := le_abs_self _
      _ = |c| ^ (d - 1) := abs_pow c (d - 1)
  exact mul_le_mul_of_nonneg_right hcle (Real.sqrt_nonneg N)

def fanCost (c n : ℝ) : ℕ → ℝ
  | 0 => 1
  | d + 1 => c * Real.sqrt n * fanCost c n d

theorem fan_cost_closed (c n : ℝ) (d : ℕ) :
    fanCost c n d = (c * Real.sqrt n) ^ d := by
  induction d with
  | zero => simp [fanCost]
  | succ d ih =>
    show c * Real.sqrt n * fanCost c n d = (c * Real.sqrt n) ^ (d + 1)
    rw [ih, pow_succ]
    ring

theorem sqrt_pow_eq (n : ℝ) (hn : 0 ≤ n) (d : ℕ) :
    Real.sqrt (n ^ d) = (Real.sqrt n) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ, pow_succ, Real.sqrt_mul (pow_nonneg hn d), ih]

theorem fan_cost_le_sqrt_pow (c n : ℝ) (hn : 0 ≤ n) (d : ℕ) :
    fanCost c n d ≤ c ^ d * Real.sqrt (n ^ d) := by
  rw [fan_cost_closed, sqrt_pow_eq n hn d, mul_pow]

theorem andOr_cost_eventually_le_log_pow (c : ℝ) (hc : 0 ≤ c) (d : ℕ) (hd : 1 ≤ d) :
    ∀ᶠ N : ℝ in Filter.atTop,
      andOrCost c N (d - 1) ≤ (Real.log N) ^ (d - 1) * Real.sqrt N := by
  have hlog : ∀ᶠ N : ℝ in Filter.atTop, c ≤ Real.log N :=
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop c)
  filter_upwards [hlog] with N hN
  rw [andOr_cost_depth c N d hd]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ hc hN (d - 1)) (Real.sqrt_nonneg N)

end Qatlib.Papers.BndErrSearch03.MainResults.AndOrTreeQueryCost
