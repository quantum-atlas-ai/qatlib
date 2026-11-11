/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

set_option backward.isDefEq.respectTransparency false

/-!
# Chebyshev additive-error bound for mean estimation

Paper: Li–Liu, arXiv:2604.00656v1, Lemma 3.

If a real estimator `X` has second central moment at most `σ²`, then
`|X - E[X]| ≥ 10σ` holds with probability at most `1/100`; equivalently the
additive error `10σ` is achieved with probability at least `0.99`.
-/

set_option autoImplicit false

namespace Qatlib.Papers.GibbsExpect26.MeanEstimation.Chebyshev

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Lemma 3, tail form: probability of error at least `10σ` is at most `1/100`. -/
theorem chebyshev_tail {X : Ω → ℝ} (hX : MemLp X 2 μ) {σ : ℝ} (hσ : 0 < σ)
    (hvar : variance X μ ≤ σ ^ 2) :
    μ {ω | 10 * σ ≤ |X ω - μ[X]|} ≤ ENNReal.ofReal (1 / 100) := by
  have hc : 0 < 10 * σ := by positivity
  refine (meas_ge_le_variance_div_sq hX hc).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hden : (10 * σ) ^ 2 = 100 * σ ^ 2 := by ring
  rw [hden]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 100 * σ ^ 2)]
  nlinarith [hvar]

/-- Lemma 3, success form: additive error `10σ` holds with probability at least
`99/100`. -/
theorem success_probability {X : Ω → ℝ} (hX : MemLp X 2 μ) {σ : ℝ} (hσ : 0 < σ)
    (hvar : variance X μ ≤ σ ^ 2) :
    ENNReal.ofReal (99 / 100) ≤ μ {ω | |X ω - μ[X]| < 10 * σ} := by
  have habs : AEStronglyMeasurable (fun ω => |X ω - μ[X]|) μ := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hX.aestronglyMeasurable.sub aestronglyMeasurable_const).norm
  have hmeas : NullMeasurableSet {ω | 10 * σ ≤ |X ω - μ[X]|} μ :=
    aestronglyMeasurable_const.nullMeasurableSet_le habs
  have hset : {ω | |X ω - μ[X]| < 10 * σ} =
      {ω | 10 * σ ≤ |X ω - μ[X]|}ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
  rw [hset, measure_compl₀ hmeas (measure_ne_top μ _), measure_univ]
  have htail := chebyshev_tail hX hσ hvar
  have hsub : 1 - ENNReal.ofReal (1 / 100) ≤
      1 - μ {ω | 10 * σ ≤ |X ω - μ[X]|} :=
    tsub_le_tsub_left htail _
  have hone : ENNReal.ofReal (99 / 100) = 1 - ENNReal.ofReal (1 / 100) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]
    norm_num
  rwa [hone]

end Qatlib.Papers.GibbsExpect26.MeanEstimation.Chebyshev
