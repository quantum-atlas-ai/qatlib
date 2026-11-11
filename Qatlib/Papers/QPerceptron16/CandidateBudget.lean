/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# Candidate sampling budgets for perceptrons

Chooses an independent candidate sample count from a positive candidate success mass and a
desired failure bound. Exponential miss estimates and a half-error allocation formalize the
candidate-budget calculation in [WiebeKapoorSvore2016], conditional on the supplied mass.

## Main statements

* `sample_failure`: For `0 < ρ ≤ 1` and positive `δ`, the selected candidate sample count makes
  `(1 - ρ)^K` at most `δ` [WiebeKapoorSvore2016].
* `half_error_budget`: Allocating `ε / 2` to candidate sampling and `ε / 2` to a second error
  contribution gives a total bound of `ε` [WiebeKapoorSvore2016].

## References

* [Wiebe et al., 2016][WiebeKapoorSvore2016]
-/

namespace Qatlib.Papers.QPerceptron16.CandidateBudget
set_option autoImplicit false
noncomputable section

/-- The candidate sample count given by the natural ceiling of `log (1 / δ) / ρ`. -/
def sampleCount (ρ δ : ℝ) : ℕ := Nat.ceil (Real.log (1/δ)/ρ)

/-- For a success mass in the interval `[0, 1]`, missing in `K` independent trials has
probability expression at most `exp (-K * ρ)`. -/
theorem miss_le_exp (ρ : ℝ) (_hρ0 : 0≤ρ) (hρ1 : ρ≤1) (K : ℕ) :
    (1-ρ)^K≤Real.exp (-(K:ℝ)*ρ) := by
  have hnn : 0≤1-ρ := by linarith
  have hh := pow_le_pow_left₀ hnn (Real.one_sub_le_exp_neg ρ) K
  calc (1-ρ)^K≤(Real.exp (-ρ))^K := hh
    _=Real.exp ((K:ℝ)*(-ρ)) := by rw [Real.exp_nat_mul]
    _=Real.exp (-(K:ℝ)*ρ) := by congr 1;ring

/-- For `0 < ρ ≤ 1` and positive `δ`, the selected candidate sample count makes `(1 - ρ)^K` at
most `δ` [WiebeKapoorSvore2016]. -/
theorem sample_failure (ρ δ : ℝ) (hρ0 : 0<ρ) (hρ1 : ρ≤1) (hδ : 0<δ) :
    (1-ρ)^sampleCount ρ δ≤δ := by
  have hm := miss_le_exp ρ hρ0.le hρ1 (sampleCount ρ δ)
  have hc : Real.log (1/δ)/ρ≤(sampleCount ρ δ:ℝ) := Nat.le_ceil _
  have hc' : Real.log (1/δ)≤(sampleCount ρ δ:ℝ)*ρ := (div_le_iff₀ hρ0).1 hc
  have he : Real.exp (-(sampleCount ρ δ:ℝ)*ρ)≤Real.exp (-Real.log (1/δ)) := by
    apply Real.exp_le_exp_of_le
    linarith
  have hi : Real.exp (-Real.log (1/δ))=δ := by simp [Real.log_inv,Real.exp_log hδ]
  exact hm.trans (he.trans hi.le)

/-- Allocating `ε / 2` to candidate sampling and `ε / 2` to a second error contribution gives a
total bound of `ε` [WiebeKapoorSvore2016]. -/
theorem half_error_budget (ρ ε : ℝ) (hρ0 : 0<ρ) (hρ1 : ρ≤1) (hε : 0<ε) :
    (1-ρ)^sampleCount ρ (ε/2)+ε/2≤ε := by
  have h := sample_failure ρ (ε/2) hρ0 hρ1 (by positivity)
  linarith

end
end Qatlib.Papers.QPerceptron16.CandidateBudget
