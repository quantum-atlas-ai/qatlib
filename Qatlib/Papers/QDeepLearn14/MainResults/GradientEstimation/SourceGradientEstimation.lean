/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# GEQAE gradient-estimation error (Theorem 2)

Source: "Quantum Deep Learning", arXiv:1412.3489v2, Theorem 2, pp.14-15
(eqs. C4-C5) and its proof.

Algorithm 4 (GEQAE) uses amplitude estimation (Theorem 3, Brassard-Høyer-Mosca-Tapp)
to learn the probabilities `P(11) = P([x_p]_i = h_j = χ = 1)` and
`P(1) = P(χ = 1)` each to relative error `Δ/8`, then forms the conditional
expectation `⟨v_i h_j⟩_data = P(11)/P(1)` (eq. C4). The error-propagation bound
(eq. C5) states that for `Δ < 1/2` the quotient differs from the true value by at
most `Δ`. Comparing the data and model expectations gives the gradient to `2Δ`,
and with `Δ = δ/(2r)` the derivative error is at most `δ`, at query cost
`Õ((κ + max_v κ_v)/δ)` and operation cost `Õ(E(κ+max_v κ_v)/δ)`.

We prove the two quantitative cores: the quotient error bound (C5) and the
derivative-error bookkeeping, plus the operation/query relation.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QDeepLearn14.MainResults.GradientEstimation

/-- **Theorem 2 (quotient error, eq. C5)** of arXiv:1412.3489 p.15. Suppose the
true conditional probabilities satisfy `0 ≤ P11 ≤ P1` with `P1 > 0`, and amplitude
estimation reports numerator and denominator with independent relative errors
`e1, e2` of magnitude at most `Δ/8` (with `0 ≤ Δ ≤ 1`). Then the estimated
quotient differs from `P11/P1` by at most `Δ`. -/
theorem theorem2_quotientError
    (P11 P1 e1 e2 Δ : ℝ)
    (hP11 : 0 ≤ P11) (hPle : P11 ≤ P1) (hP1 : 0 < P1)
    (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1)
    (he1 : |e1| ≤ Δ / 8) (he2 : |e2| ≤ Δ / 8) (he2pos : 0 < 1 + e2) :
    |P11 * (1 + e1) / (P1 * (1 + e2)) - P11 / P1| ≤ Δ := by
  have hPratio0 : 0 ≤ P11 / P1 := div_nonneg hP11 hP1.le
  have hPratio1 : P11 / P1 ≤ 1 := (div_le_one hP1).mpr hPle
  -- Rewrite the difference as a ratio times `(e1 - e2)/(1 + e2)`.
  have hd : P11 * (1 + e1) / (P1 * (1 + e2)) - P11 / P1
      = (P11 / P1) * ((e1 - e2) / (1 + e2)) := by
    field_simp [hP1.ne', he2pos.ne']
    ring
  -- Triangle bound on the perturbation of the ratio.
  have he12 : |e1 - e2| ≤ Δ / 4 := by
    calc |e1 - e2| = |e1 + -e2| := by ring_nf
      _ ≤ |e1| + |-e2| := abs_add_le _ _
      _ = |e1| + |e2| := by rw [abs_neg]
      _ ≤ Δ / 8 + Δ / 8 := add_le_add he1 he2
      _ = Δ / 4 := by ring
  have hdabs : |(e1 - e2) / (1 + e2)| ≤ (Δ / 4) / (1 + e2) := by
    rw [abs_div, abs_of_pos he2pos]
    exact (div_le_div_iff_of_pos_right he2pos).mpr he12
  -- `(Δ/4)/(1+e2) ≤ Δ`: since `e2 ≥ -Δ/8 ≥ -1/8`.
  have hratio : (Δ / 4) / (1 + e2) ≤ Δ := by
    rw [div_le_iff₀ he2pos]
    have he2low : -(1:ℝ) / 8 ≤ e2 := by
      have h := (abs_le.mp he2).1
      nlinarith [hΔ1, h]
    nlinarith [he2low, hΔ0, hΔ1]
  calc |P11 * (1 + e1) / (P1 * (1 + e2)) - P11 / P1|
      = (P11 / P1) * |(e1 - e2) / (1 + e2)| := by rw [hd, abs_mul, abs_of_nonneg hPratio0]
    _ ≤ 1 * |(e1 - e2) / (1 + e2)| :=
        mul_le_mul_of_nonneg_right hPratio1 (abs_nonneg _)
    _ = |(e1 - e2) / (1 + e2)| := one_mul _
    _ ≤ (Δ / 4) / (1 + e2) := hdabs
    _ ≤ Δ := hratio

/-- **Theorem 2 (derivative error)** of arXiv:1412.3489 p.15: with learning rate
`r > 0` and amplitude-estimation error `Δ = δ/(2r)`, the `2Δr` gradient error is
at most `δ`. -/
theorem theorem2_gradientError
    (Δ r δ : ℝ) (hr : 0 < r) (hΔ : Δ = δ / (2 * r)) :
    2 * Δ * r ≤ δ := by
  rw [hΔ]
  have heq : 2 * (δ / (2 * r)) * r = δ := by
    field_simp [hr.ne']
  rw [heq]

/-- **Theorem 2 (operation count relation)** of arXiv:1412.3489 p.15: each state
preparation costs `Õ(E)` operations and one query to `U_O`, so the operation
count is `E` times the query count `(κ + max_v κ_v)/δ`. -/
theorem theorem2_operationScaling
    (E κ maxκ δ : ℝ) (hδ : δ ≠ 0) :
    E * ((κ + maxκ) / δ) = E * (κ + maxκ) / δ := by
  field_simp [hδ]

end Qatlib.Papers.QDeepLearn14.MainResults.GradientEstimation
