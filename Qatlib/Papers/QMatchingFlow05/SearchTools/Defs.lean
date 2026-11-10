/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.BigOperators.Field

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QMatchingFlow05.SearchTools

def searchCost (c N : ℝ) : ℝ := c * Real.sqrt N

def logFactor (n : ℕ) : ℝ := Real.log ((n : ℝ) + 3)

theorem logFactor_pos (n : ℕ) : 0 < logFactor n := by
  unfold logFactor
  apply Real.log_pos
  have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

theorem one_le_logFactor (n : ℕ) : 1 ≤ logFactor n := by
  unfold logFactor
  rw [Real.le_log_iff_exp_le (by positivity)]
  have h3 : Real.exp 1 < 3 := Real.exp_one_lt_three
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

theorem sum_sqrt_mul_le {ι : Type*} [Fintype ι] (f g : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) :
    ∑ i, Real.sqrt (f i * g i) ≤
      Real.sqrt (∑ i, f i) * Real.sqrt (∑ i, g i) := by
  calc ∑ i, Real.sqrt (f i * g i)
      = ∑ i, Real.sqrt (f i) * Real.sqrt (g i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Real.sqrt_mul (hf i)]
    _ ≤ Real.sqrt (∑ i, f i) * Real.sqrt (∑ i, g i) :=
        Real.sum_sqrt_mul_sqrt_le Finset.univ hf hg

def adjacencyVertexCost (c : ℝ) (n : ℕ) : ℝ := 2 * searchCost c (n : ℝ) * logFactor n

def listVertexCost (c nV dV : ℝ) : ℝ :=
  c * (Real.sqrt (nV * dV) + Real.sqrt (dV + 1))

end Qatlib.Papers.QMatchingFlow05.SearchTools

end
