/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LatentPQCTran26.MainResults.Overlap

/-!
# Coverage from a lower bound on the mean

`reverse_markov` bounds the measure of the superlevel set `gradRichSet` using an integral lower
bound and a pointwise upper bound. The auxiliary estimate `coverage_arithmetic` specializes the
numerical comparison used in the coverage argument. See [TranEtAl2026] for the paper context.

## Main statements

* `reverse_markov`: For an integrable nonnegative function bounded by `B` on a probability
  space, with mean at least `μ0` and measurable superlevel set at `t < B`, that set has real
  measure at least `(μ0 - t) / (B - t)`.
* `coverage_arithmetic`: If `μ0 ≥ 0`, `K > 0`, and `μ0 / 2 < 4 * K`, then `μ0 / (8 * K) ≤ (μ0 /
  2) / (4 * K - μ0 / 2)`.

## References

* [Tran et al., 2026][TranEtAl2026]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace Qatlib.Papers.LatentPQCTran26.MainResults.Coverage

open Qatlib.Papers.LatentPQCTran26.MainResults.Overlap

/-- For an integrable nonnegative function bounded by `B` on a probability space, with mean at
least `μ0` and measurable superlevel set at `t < B`, that set has real measure at least `(μ0
- t) / (B - t)` [TranEtAl2026]. -/
theorem reverse_markov
    {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) [IsProbabilityMeasure ν]
    (F : Θ → ℝ) (B t μ0 : ℝ)
    (hF_int : Integrable F ν) (h_nonneg : ∀ θ, 0 ≤ F θ) (hB : ∀ θ, F θ ≤ B)
    (hmean : μ0 ≤ ∫ θ, F θ ∂ν)
    (hS : MeasurableSet (gradRichSet F t))
    (htB : t < B) :
    (μ0 - t) / (B - t) ≤ ν.real (gradRichSet F t) := by
  have hsplit := integral_add_compl hS hF_int

  have hS_nonneg : 0 ≤ ∫ θ in gradRichSet F t, F θ ∂ν :=
    setIntegral_nonneg hS (fun θ _ => h_nonneg θ)
  have hS_le : ∫ θ in gradRichSet F t, F θ ∂ν ≤ B * ν.real (gradRichSet F t) := by
    have h1 : ‖∫ θ in gradRichSet F t, F θ ∂ν‖ ≤ B * ν.real (gradRichSet F t) := by
      apply norm_setIntegral_le_of_norm_le_const (by finiteness)
      intro θ _
      rw [Real.norm_eq_abs, abs_of_nonneg (h_nonneg θ)]
      exact hB θ
    rwa [Real.norm_eq_abs, abs_of_nonneg hS_nonneg] at h1

  have hSc_nonneg : 0 ≤ ∫ θ in (gradRichSet F t)ᶜ, F θ ∂ν :=
    setIntegral_nonneg hS.compl (fun θ _ => h_nonneg θ)
  have hSc_le : ∫ θ in (gradRichSet F t)ᶜ, F θ ∂ν ≤ t * ν.real (gradRichSet F t)ᶜ := by
    have h1 : ‖∫ θ in (gradRichSet F t)ᶜ, F θ ∂ν‖ ≤ t * ν.real (gradRichSet F t)ᶜ := by
      apply norm_setIntegral_le_of_norm_le_const (by finiteness)
      intro θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (h_nonneg θ)]
      have hlt : ¬ (t ≤ F θ) := hθ
      push Not at hlt
      linarith
    rwa [Real.norm_eq_abs, abs_of_nonneg hSc_nonneg] at h1

  have hbound : μ0 ≤ B * ν.real (gradRichSet F t) + t * ν.real (gradRichSet F t)ᶜ := by
    have hle : ∫ θ, F θ ∂ν ≤
        B * ν.real (gradRichSet F t) + t * ν.real (gradRichSet F t)ᶜ := by
      rw [← hsplit]; linarith [hS_le, hSc_le]
    linarith [hmean, hle]
  have hcompl : ν.real (gradRichSet F t)ᶜ = 1 - ν.real (gradRichSet F t) := by
    rw [measureReal_compl hS, probReal_univ]
  have hmain : μ0 ≤ t + (B - t) * ν.real (gradRichSet F t) := by
    rw [hcompl] at hbound
    nlinarith [hbound]
  have hBt : 0 < B - t := by linarith
  rw [div_le_iff₀ hBt]
  nlinarith [hmain]

/-- If `μ0 ≥ 0`, `K > 0`, and `μ0 / 2 < 4 * K`, then `μ0 / (8 * K) ≤ (μ0 / 2) / (4 * K - μ0 /
2)`. -/
theorem coverage_arithmetic (μ0 : ℝ) (K : ℝ) (hμ0 : 0 ≤ μ0)
    (hK : 0 < K) (hsml : μ0 / 2 < 4 * K) :
    μ0 / (8 * K) ≤ (μ0 / 2) / (4 * K - μ0 / 2) := by
  have hpos : 0 < 4 * K - μ0 / 2 := by linarith
  have hden : 0 < 8 * K := by positivity
  rw [le_div_iff₀ hpos, div_mul_eq_mul_div, div_le_iff₀ hden]
  nlinarith [hμ0, hK, hsml]

end Qatlib.Papers.LatentPQCTran26.MainResults.Coverage
