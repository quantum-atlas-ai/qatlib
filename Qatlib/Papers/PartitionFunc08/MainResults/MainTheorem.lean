/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PartitionFunc08.MainResults.ProductComposition
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Composition of partition-function estimators

The theorem `theorem2_composite_scheme` combines per-ratio accuracy events into relative
accuracy for a scaled product with probability at least three quarters. The companion cost
estimate bounds samples and reflection use from the stated per-ratio budgets. These estimates
form part of the partition-function scheme in [WocjanEtAl2009a].

## Main statements

* `theorem2_composite_scheme`: For positive ratios, positive scale `Z0`, and `0 < ε ≤ 1`,
  per-ratio relative error `ε / (2 * ℓ)` with success at least `1 - 1 / (4 * ℓ)` yields relative
  error `ε` for the scaled product with success at least three quarters.
* `theorem2_per_ratio_costs`: For positive `ℓ` and `ε`, the assumed sample and per-sample
  reflection budgets imply at most `log (4 * ℓ)` samples and at most `(2 * ℓ / ε) * log (4 * ℓ)`
  total reflections.

## References

* [Wocjan et al., 2009][WocjanEtAl2009a]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal Topology BigOperators

namespace Qatlib.Papers.PartitionFunc08.MainResults.MainTheorem

/-- For positive ratios, positive scale `Z0`, and `0 < ε ≤ 1`, per-ratio relative error `ε / (2
* ℓ)` with success at least `1 - 1 / (4 * ℓ)` yields relative error `ε` for the scaled
product with success at least three quarters. See [Wocjan et al., 2009][WocjanEtAl2009a]. -/
theorem theorem2_composite_scheme
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℓ : ℕ) (hℓ : 0 < ℓ) {ε Z0 : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hZ0 : 0 < Z0)
    (α : Fin ℓ → ℝ) (Q : Fin ℓ → Ω → ℝ) (hα : ∀ i, 0 < α i) (hQ : ∀ i, Measurable (Q i))
    (hacc : ∀ i,
      1 - 1 / (4 * (ℓ : ℝ)) ≤
        μ.real (relAccEvent (α i) (ε / (2 * (ℓ : ℝ))) (Q i))) :
    3 / 4 ≤ μ.real (relAccEvent (Z0 * ∏ i, α i) ε (fun ω => Z0 * ∏ i, Q i ω)) := by
  refine (Qatlib.Papers.PartitionFunc08.MainResults.ProductComposition.lemma3_product_composition
    μ ℓ hℓ hε0 hε1 α Q hα hQ hacc).trans ?_
  refine measureReal_mono ?_
  intro ω hω
  simp only [relAccEvent, Set.mem_setOf_eq] at hω ⊢
  have hP : 0 < ∏ i, α i := Finset.prod_pos (fun i _ => hα i)
  constructor
  · calc (1 - ε) * (Z0 * ∏ i, α i) = Z0 * ((1 - ε) * ∏ i, α i) := by ring
      _ ≤ Z0 * ∏ i, Q i ω := mul_le_mul_of_nonneg_left hω.1 hZ0.le
  · calc Z0 * ∏ i, Q i ω ≤ Z0 * ((1 + ε) * ∏ i, α i) :=
        mul_le_mul_of_nonneg_left hω.2 hZ0.le
      _ = (1 + ε) * (Z0 * ∏ i, α i) := by ring

/-- For positive `ℓ` and `ε`, the assumed sample and per-sample reflection budgets imply at most
`log (4 * ℓ)` samples and at most `(2 * ℓ / ε) * log (4 * ℓ)` total reflections. See [Wocjan
et al., 2009][WocjanEtAl2009a]. -/
theorem theorem2_per_ratio_costs
    {ℓ : ℕ} (hℓ : 0 < ℓ) {ε : ℝ} (hε : 0 < ε)
    {samples reflPerSample : ℝ} (hs0 : 0 ≤ samples) (hr0 : 0 ≤ reflPerSample)
    (hs : samples ≤ Real.log (4 * (ℓ : ℝ)))
    (hr : reflPerSample ≤ 1 / (ε / (2 * (ℓ : ℝ)))) :
    samples ≤ Real.log (4 * (ℓ : ℝ)) ∧
      samples * reflPerSample ≤ (2 * (ℓ : ℝ) / ε) * Real.log (4 * (ℓ : ℝ)) := by
  have hlog : 0 ≤ Real.log (4 * (ℓ : ℝ)) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
    linarith
  have h1 : 1 / (ε / (2 * (ℓ : ℝ))) = 2 * (ℓ : ℝ) / ε := by
    rw [div_div_eq_mul_div, one_mul]
  rw [h1] at hr
  refine ⟨hs, ?_⟩
  calc samples * reflPerSample ≤ Real.log (4 * (ℓ : ℝ)) * (2 * (ℓ : ℝ) / ε) :=
        mul_le_mul hs hr hr0 hlog
    _ = (2 * (ℓ : ℝ) / ε) * Real.log (4 * (ℓ : ℝ)) := by ring

end Qatlib.Papers.PartitionFunc08.MainResults.MainTheorem
