/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PhaseEst07.MainResults.WindowState

open scoped BigOperators

noncomputable def sourceUniformVector (q : ℕ) : ℕ → ℝ := fun _ => 1 / Real.sqrt (q : ℝ)

noncomputable def sourceWindowCost (q : ℕ) (ε : ℝ) (x : ℕ → ℝ) : ℝ :=
  (1 - ε / Real.pi) -
    (ε / (2 * Real.pi)) *
      ((∑ k ∈ Finset.range q, x k) ^ 2 - ∑ k ∈ Finset.range q, (x k) ^ 2)

theorem source_uniform_vector_normalized (q : ℕ) (hq : 1 ≤ q) :
    ∑ k ∈ Finset.range q, (sourceUniformVector q k) ^ 2 = 1 := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hterm : ∀ k ∈ Finset.range q, (sourceUniformVector q k) ^ 2 = 1 / (q : ℝ) := by
    intro k _
    unfold sourceUniformVector
    rw [div_pow, Real.sq_sqrt (le_of_lt hqpos), one_pow]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

theorem source_uniform_vector_sum (q : ℕ) (hq : 1 ≤ q) :
    ∑ k ∈ Finset.range q, sourceUniformVector q k = Real.sqrt (q : ℝ) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hsq : Real.sqrt (q : ℝ) * Real.sqrt (q : ℝ) = (q : ℝ) := Real.mul_self_sqrt (le_of_lt hqpos)
  have hsqne : Real.sqrt (q : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hqpos)
  unfold sourceUniformVector
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one_div, div_eq_iff hsqne, hsq]

theorem source_window_cost_uniform (q : ℕ) (hq : 1 ≤ q) (ε : ℝ) :
    sourceWindowCost q ε (sourceUniformVector q)
      = 1 - ε * ((q : ℝ) + 1) / (2 * Real.pi) := by
  have hs := source_uniform_vector_sum q hq
  have hn := source_uniform_vector_normalized q hq
  unfold sourceWindowCost
  rw [hs, hn, Real.sq_sqrt (by positivity)]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

theorem source_window_cost_uniform_optimal (q : ℕ) (hq : 1 ≤ q) (ε : ℝ) (hε : 0 ≤ ε)
    (x : ℕ → ℝ) (hx : ∑ k ∈ Finset.range q, (x k) ^ 2 = 1) :
    sourceWindowCost q ε x ≥ sourceWindowCost q ε (sourceUniformVector q) := by
  have hs := source_uniform_vector_sum q hq
  have hn := source_uniform_vector_normalized q hq

  have hcs : (∑ k ∈ Finset.range q, x k) ^ 2 ≤ (q : ℝ) * ∑ k ∈ Finset.range q, (x k) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.range q) (f := x)
    simpa [Finset.card_range] using this
  rw [hx] at hcs
  have hcs' : (∑ k ∈ Finset.range q, x k) ^ 2 ≤ (q : ℝ) := by simpa using hcs

  have hupper : (∑ k ∈ Finset.range q, sourceUniformVector q k) ^ 2 = (q : ℝ) := by
    rw [hs]; exact Real.sq_sqrt (by positivity)
  have hcoef : 0 ≤ ε / (2 * Real.pi) := by
    apply div_nonneg hε; positivity
  unfold sourceWindowCost
  rw [hupper, hn]
  have hxeq : ∑ k ∈ Finset.range q, (x k) ^ 2 = 1 := hx
  rw [hxeq]

  have hmono : (ε / (2 * Real.pi)) * ((∑ k ∈ Finset.range q, x k) ^ 2 - 1)
      ≤ (ε / (2 * Real.pi)) * ((q : ℝ) - 1) := by
    apply mul_le_mul_of_nonneg_left _ hcoef
    linarith [hcs']
  linarith [hmono]

end Qatlib.Papers.PhaseEst07.MainResults.WindowState
