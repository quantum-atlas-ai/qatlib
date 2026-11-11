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

/-!
# Finite cosine sums for amplification windows

This module evaluates finite cosine sums on arithmetic progressions, including the odd-multiple
sum used in amplitude amplification. `cosine_arithmetic_sum_mul` and `cosine_odd_sum_mul` retain
the sine factor, so their identities also apply when that factor vanishes.

The mathematical background is described in [BoyerEtAl1998].

## Main statements

* `cosine_arithmetic_sum`: evaluates an arithmetic cosine sum when its sine denominator is
  nonzero.
* `cosine_odd_sum`: evaluates the sum of the first `m` odd cosine multiples.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

namespace Qatlib.Concepts.LchsSimulation.StaticLchs

open scoped BigOperators

/-- The product `2 * sin y * cos x` equals `sin (x + y) - sin (x - y)`. -/
private theorem two_sin_mul_cos (x y : ℝ) :
    2 * Real.sin y * Real.cos x = Real.sin (x + y) - Real.sin (x - y) := by
  rw [Real.sin_add, Real.sin_sub]
  ring

/-- The arithmetic cosine sum multiplied by `sin β` equals `sin (m * β) * cos (α + (m - 1) * β)`
[Boyer et al., Lemma 1][BoyerEtAl1998]. -/
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

/-- When `sin β ≠ 0`, the arithmetic cosine sum equals `sin (m * β) * cos (α + (m - 1) * β) /
sin β` [Boyer et al., Lemma 1][BoyerEtAl1998]. -/
theorem cosine_arithmetic_sum (α β : ℝ) (m : ℕ) (hβ : Real.sin β ≠ 0) :
    (∑ j ∈ Finset.range m, Real.cos (α + 2 * β * j)) =
      Real.sin (m * β) * Real.cos (α + ((m : ℝ) - 1) * β) / Real.sin β := by
  apply (eq_div_iff hβ).2
  simpa only [mul_comm] using cosine_arithmetic_sum_mul α β m

/-- Multiplying the sum of `cos ((2 * j + 1) * α)` for `j < m` by `2 * sin α` gives `sin (2 * m
* α)` [Boyer et al., Lemma 1][BoyerEtAl1998]. -/
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

/-- When `sin α ≠ 0`, the sum of `cos ((2 * j + 1) * α)` for `j < m` equals `sin (2 * m * α) /
(2 * sin α)` [Boyer et al., Lemma 1][BoyerEtAl1998]. -/
theorem cosine_odd_sum (α : ℝ) (m : ℕ) (hα : Real.sin α ≠ 0) :
    (∑ j ∈ Finset.range m, Real.cos ((2 * j + 1) * α)) =
      Real.sin (2 * m * α) / (2 * Real.sin α) := by
  apply (eq_div_iff (mul_ne_zero (by norm_num) hα)).2
  simpa only [mul_comm] using cosine_odd_sum_mul α m

end Qatlib.Concepts.LchsSimulation.StaticLchs
