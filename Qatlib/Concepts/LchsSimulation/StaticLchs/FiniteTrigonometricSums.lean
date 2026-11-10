/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Lean.Elab.Tactic.NormCast
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Qatlib.Concepts.LchsSimulation.StaticLchs

open scoped BigOperators

private theorem two_sin_mul_cos (x y : ℝ) :
    2 * Real.sin y * Real.cos x = Real.sin (x + y) - Real.sin (x - y) := by
  rw [Real.sin_add, Real.sin_sub]
  ring

theorem cosine_arithmetic_sum_mul (α β : ℝ) (m : ℕ) :
    Real.sin β * (∑ j ∈ Finset.range m, Real.cos (α + 2 * β * j)) =
      Real.sin (m * β) * Real.cos (α + ((m : ℝ) - 1) * β) := by
  have telescoping (n : ℕ) :
      2 * Real.sin β * (∑ j ∈ Finset.range n, Real.cos (α + 2 * β * j)) =
        Real.sin (α + (2 * (n : ℝ) - 1) * β) - Real.sin (α - β) := by
    induction n with
    | zero => simp [sub_eq_add_neg]
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih, two_sin_mul_cos]
      have hp : α + 2 * β * (n : ℝ) + β =
          α + (2 * (n + 1 : ℕ) - 1) * β := by push_cast; ring
      have hm : α + 2 * β * (n : ℝ) - β =
          α + (2 * (n : ℝ) - 1) * β := by ring
      rw [hp, hm]
      ring
  have hp : α + ((m : ℝ) - 1) * β + m * β =
      α + (2 * (m : ℝ) - 1) * β := by ring
  have hm : α + ((m : ℝ) - 1) * β - m * β = α - β := by ring
  have product := two_sin_mul_cos (α + ((m : ℝ) - 1) * β) (m * β)
  rw [hp, hm] at product
  nlinarith [telescoping m]

theorem cosine_arithmetic_sum (α β : ℝ) (m : ℕ) (hβ : Real.sin β ≠ 0) :
    (∑ j ∈ Finset.range m, Real.cos (α + 2 * β * j)) =
      Real.sin (m * β) * Real.cos (α + ((m : ℝ) - 1) * β) / Real.sin β := by
  apply (eq_div_iff hβ).2
  simpa only [mul_comm] using cosine_arithmetic_sum_mul α β m

theorem cosine_odd_sum_mul (α : ℝ) (m : ℕ) :
    (2 * Real.sin α) * (∑ j ∈ Finset.range m, Real.cos ((2 * j + 1) * α)) =
      Real.sin (2 * m * α) := by
  have h := cosine_arithmetic_sum_mul α α m
  have sum_eq : (∑ j ∈ Finset.range m, Real.cos (α + 2 * α * j)) =
      ∑ j ∈ Finset.range m, Real.cos ((2 * j + 1) * α) := by
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    ring
  rw [sum_eq, show α + ((m : ℝ) - 1) * α = m * α by ring] at h
  have double : Real.sin (2 * m * α) =
      2 * Real.sin (m * α) * Real.cos (m * α) := by
    rw [show 2 * (m : ℝ) * α = 2 * (m * α) by ring, Real.sin_two_mul]
  rw [double]
  nlinarith [h]

theorem cosine_odd_sum (α : ℝ) (m : ℕ) (hα : Real.sin α ≠ 0) :
    (∑ j ∈ Finset.range m, Real.cos ((2 * j + 1) * α)) =
      Real.sin (2 * m * α) / (2 * Real.sin α) := by
  apply (eq_div_iff (mul_ne_zero (by norm_num) hα)).2
  simpa only [mul_comm] using cosine_odd_sum_mul α m

end Qatlib.Concepts.LchsSimulation.StaticLchs
