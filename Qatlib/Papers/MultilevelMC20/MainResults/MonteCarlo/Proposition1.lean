/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MultilevelMC20.MainResults.CostModel.CostAsymptotics

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 1: complexity of classical Monte Carlo with a strong-order scheme

An, Linden, Liu, Montanaro, Shao, Wang,
*Quantum-accelerated multilevel Monte Carlo methods for stochastic differential equations
in mathematical finance*, fixed arXiv:2012.06283v2 (accepted in Quantum 2021-06-16).

Paper Proposition 1 (p. 6) with proof (2.5)--(2.8):

> Let `Y` be an estimator of `E[P(X_T)]` with bounded variance, based on a numerical
> discretization with time step size `h` using a numerical scheme with strong order `r`.
> Then in order to achieve the accuracy of mean-squared error `ε²`, the computational
> complexity of the Monte Carlo method is `O(ε^{-2-1/r})`.

Formalisation of the proof's numerical content: the variance contribution of `N` samples
is `σ²/N` (2.6), the squared bias is `O(h^{2r})` (2.7), so the MSE is
`σ²/N + B²h^{2r}` (2.8).  Choosing `N = 2σ²ε^{-2}` and `h = (ε/(2B))^{1/r}` makes the
MSE at most `ε²`, and the cost `N/h = (2σ²ε^{-2})/(ε/(2B))^{1/r}` is
`2σ²(2B)^{1/r} ε^{-2-1/r}`, i.e. in the cost class `(2 + 1/r, 0, 0)`.
-/

set_option autoImplicit false
noncomputable section

open Filter Asymptotics
open scoped Topology BigOperators

namespace Qatlib.Papers.MultilevelMC20.MainResults

/-- Proposition 1 (p. 6, eqs. (2.5)--(2.8)): classical MC with a strong-order-`r` scheme
attains mean-squared error `ε²` at cost `O(ε^{-2-1/r})`.

The hypotheses `hr`, `hB`, `hσ` are the positivity of the strong order `r`, of the bias
constant `B` (so that `h = (ε/(2B))^{1/r}` is meaningful) and of the per-sample variance
bound `σ²`.  The conclusion records the explicit schedule `N = 2σ²/ε²`,
`h = (ε/(2B))^{1/r}` and the resulting cost class. -/
theorem proposition1
    {r B σ : ℝ} (hr : 0 < r) (hB : 0 < B) (hσ : 0 < σ) :
    ∃ cost : ℝ → ℝ, CostClass (2 + 1 / r) 0 0 cost ∧
      ∀ᶠ ε : ℝ in epsZero,
        σ ^ 2 / (2 * σ ^ 2 / ε ^ 2) +
            B ^ 2 * ((ε / (2 * B)) ^ (1 / r)) ^ (2 * r) ≤ ε ^ 2 ∧
        cost ε = (2 * σ ^ 2 / ε ^ 2) / ((ε / (2 * B)) ^ (1 / r)) := by
  refine ⟨fun ε => (2 * σ ^ 2 * (2 * B) ^ (1 / r)) * ε ^ (-(2 + 1 / r)),
    costClass_const_rpow _ _, ?_⟩
  filter_upwards [eventually_pos_epsZero] with ε hε
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hB0 : B ≠ 0 := ne_of_gt hB
  have hσ0 : σ ≠ 0 := ne_of_gt hσ
  have hε0 : ε ≠ 0 := ne_of_gt hε
  have h2B : 0 < 2 * B := by positivity
  have h2B0 : (2 * B) ^ (1 / r) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos h2B _)
  have hεr0 : ε ^ (1 / r) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hε _)
  have hbase : 0 < ε / (2 * B) := by positivity
  have hpow : ((ε / (2 * B)) ^ (1 / r)) ^ (2 * r) = (ε / (2 * B)) ^ 2 := by
    rw [← Real.rpow_mul hbase.le]
    rw [show (1 / r) * (2 * r) = 2 by field_simp]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hbiasSq : B ^ 2 * ((ε / (2 * B)) ^ (1 / r)) ^ (2 * r) = ε ^ 2 / 4 := by
    rw [hpow]
    field_simp
    ring
  have hvar : σ ^ 2 / (2 * σ ^ 2 / ε ^ 2) = ε ^ 2 / 2 := by
    field_simp
  constructor
  · rw [hvar, hbiasSq]
    nlinarith [sq_nonneg ε]
  · have hdiv : (ε / (2 * B)) ^ (1 / r)
        = (ε ^ (1 / r)) * ((2 * B) ^ (1 / r))⁻¹ := by
      rw [Real.div_rpow hε.le h2B.le, div_eq_mul_inv]
    have hexp : -(2 + 1 / r) = (-2 : ℝ) + -(1 / r) := by ring
    have hsplit : ε ^ (-(2 + 1 / r)) = (ε ^ (-2 : ℝ)) * (ε ^ (-(1 / r))) := by
      rw [hexp, Real.rpow_add hε]
    rw [hdiv, hsplit, Real.rpow_neg hε.le, Real.rpow_neg hε.le, ← Real.rpow_two]
    field_simp
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

end Qatlib.Papers.MultilevelMC20.MainResults
