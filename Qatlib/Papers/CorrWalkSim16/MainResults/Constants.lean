/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.Order.IntermediateValue

set_option backward.isDefEq.respectTransparency false

/-!
# CorrWalkSim16: the numerical constants `ζ` of Lemmas 4 and 5

Berry--Novo, arXiv:1606.03443v3, Lemma 4 (Eq. (65)) and Lemma 5 (Eq. (82))
introduce the constant

  `ζ ≈ 1.8`, the solution of `e^{1 + 1/(2ζ)} = 2ζ`,

because the tail bound `∑_{|m|>M} |J_m(z)| x^m ≤ 1/2` of Eq. (68) is evaluated
at `x = M/(zζ)`, and the choice of `ζ` is what makes the right-hand side
decrease with `M`.

This file proves that such a `ζ` exists in the interval `(3/2, 2)`:
`exists_zeta_root` gives `ζ` with `3/2 < ζ`, `ζ < 2` and
`Real.exp (1 + 1/(2ζ)) = 2ζ`, so the paper's constant is not an unexplained
numerical input.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Qatlib.Papers.CorrWalkSim16.MainResults

/-- The function whose root defines the paper's constant `ζ`. -/
def zetaEq (ζ : ℝ) : ℝ := Real.exp (1 + 1 / (2 * ζ)) - 2 * ζ

/-- `e^{5/4} < 4`, from `(e^{5/4})^4 = e^5 < 3^5 < 4^4`. -/
theorem exp_five_quarters_lt_four : Real.exp (5 / 4) < 4 := by
  have h4 : Real.exp (5 / 4) ^ 4 = Real.exp 5 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hexp1 : Real.exp 1 ^ 5 < 243 := by
    have hlt : Real.exp 1 ^ 5 < (3 : ℝ) ^ 5 :=
      pow_lt_pow_left₀ Real.exp_one_lt_three (le_of_lt (Real.exp_pos 1)) (by norm_num)
    have h3 : (3 : ℝ) ^ 5 = 243 := by norm_num
    rw [h3] at hlt
    exact hlt
  have h5 : Real.exp 5 < 243 := by
    have heq : Real.exp 5 = Real.exp 1 ^ 5 := by
      rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
    rw [heq]
    exact hexp1
  by_contra hge
  push Not at hge
  have h256 : (4 : ℝ) ^ 4 ≤ Real.exp (5 / 4) ^ 4 :=
    pow_le_pow_left₀ (by norm_num) hge 4
  rw [h4] at h256
  norm_num at h256
  linarith

/-- `e^{4/3} > 3`, from the fourth partial sum of the exponential series. -/
theorem three_lt_exp_four_thirds : (3 : ℝ) < Real.exp (4 / 3) := by
  have hsum := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 3) 4
  have hval : (∑ i ∈ Finset.range 4, (4 / 3 : ℝ) ^ i / (i.factorial : ℝ))
      = 1 + 4 / 3 + (4 / 3) ^ 2 / 2 + (4 / 3) ^ 3 / 6 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hval] at hsum
  linarith

/-- The paper's constant `ζ`: there is `ζ ∈ (3/2, 2)` with
`e^{1 + 1/(2ζ)} = 2ζ` (numerically `ζ ≈ 1.79`). -/
theorem exists_zeta_root :
    ∃ ζ : ℝ, 3 / 2 < ζ ∧ ζ < 2 ∧ Real.exp (1 + 1 / (2 * ζ)) = 2 * ζ := by
  have hden : ∀ x ∈ Set.Icc (3 / 2 : ℝ) 2, (2 * x) ≠ 0 := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    positivity
  have hinner : ContinuousOn (fun ζ : ℝ => 1 + 1 / (2 * ζ)) (Set.Icc (3 / 2 : ℝ) 2) := by
    refine ContinuousOn.add continuousOn_const ?_
    exact ContinuousOn.div continuousOn_const (by fun_prop) hden
  have hcont : ContinuousOn zetaEq (Set.Icc (3 / 2 : ℝ) 2) := by
    refine ContinuousOn.sub ?_ (by fun_prop)
    exact Real.continuous_exp.comp_continuousOn hinner
  have hpos : 0 < zetaEq (3 / 2) := by
    have h : zetaEq (3 / 2) = Real.exp (4 / 3) - 3 := by
      unfold zetaEq
      norm_num
    rw [h]
    linarith [three_lt_exp_four_thirds]
  have hneg : zetaEq 2 < 0 := by
    have h : zetaEq 2 = Real.exp (5 / 4) - 4 := by
      unfold zetaEq
      norm_num
    rw [h]
    linarith [exp_five_quarters_lt_four]
  obtain ⟨c, hc, hroot⟩ :=
    intermediate_value_Ioo' (show (3 / 2 : ℝ) ≤ 2 by norm_num) hcont ⟨hneg, hpos⟩
  refine ⟨c, hc.1, hc.2, ?_⟩
  have hsub := sub_eq_zero.mp hroot
  unfold zetaEq at hsub
  linarith

end Qatlib.Papers.CorrWalkSim16.MainResults
