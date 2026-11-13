/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LatentPQCTran26.MainResults.Coverage
import Qatlib.Papers.LatentPQCTran26.MainResults.Trainability

/-!
# Warm-start integral bounds from reference coverage

`corollary14` transfers reference coverage of a superlevel set to a weighted mixture with a
training measure. For a nonnegative integrable function, it yields an explicit integral lower
bound using the threshold `μ0 / 2` and reference coverage `μ0 / (8 * K)`. See [TranEtAl2026] for
the paper context.

## Main statements

* `corollary14`: Under the stated finiteness, sign, measurability, and integrability hypotheses,
  reference superlevel coverage at least `μ0 / (8 * K)` gives mixture integral at least `(μ0 /
  2) * (lam * μ0 / (8 * K))`.

## References

* [Tran et al., 2026][TranEtAl2026]
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace Qatlib.Papers.LatentPQCTran26.MainResults.WarmStart

open Qatlib.Papers.LatentPQCTran26.MainResults.Overlap
open Qatlib.Papers.LatentPQCTran26.MainResults.Trainability

/-- Under the stated finiteness, sign, measurability, and integrability hypotheses, reference
superlevel coverage at least `μ0 / (8 * K)` gives mixture integral at least `(μ0 / 2) * (lam
* μ0 / (8 * K))` [TranEtAl2026]. -/
theorem corollary14
    {Θ : Type*} [MeasurableSpace Θ]
    (ν pt : Measure Θ) [IsProbabilityMeasure ν] [IsProbabilityMeasure pt]
    (lam : NNReal) (F : Θ → ℝ) (μ0 K : ℝ) (_hK : 0 < K) (_hμ0 : 0 ≤ μ0)
    [IsFiniteMeasure (lam • ν + (1 - lam) • pt)]
    (hc : 0 ≤ μ0 / 2) (_hq : 0 ≤ (lam : ℝ) * (μ0 / (8 * K)))
    (hS : MeasurableSet (gradRichSet F (μ0 / 2)))
    (hF_int : Integrable F (lam • ν + (1 - lam) • pt))
    (hF_nonneg : ∀ θ, 0 ≤ F θ)
    (hνS : μ0 / (8 * K) ≤ ν.real (gradRichSet F (μ0 / 2))) :
    (μ0 / 2) * ((lam : ℝ) * (μ0 / (8 * K)))
      ≤ ∫ θ, F θ ∂(lam • ν + (1 - lam) • pt) := by

  have hsmul : (lam • ν).real (gradRichSet F (μ0 / 2))
      = (lam : ℝ) * ν.real (gradRichSet F (μ0 / 2)) := by
    rw [measureReal_nnreal_smul_apply]
  have hsecond : 0 ≤ ((1 - lam) • pt).real (gradRichSet F (μ0 / 2)) :=
    measureReal_nonneg
  have hcover : (lam : ℝ) * (μ0 / (8 * K))
      ≤ (lam • ν + (1 - lam) • pt).real (gradRichSet F (μ0 / 2)) := by
    rw [measureReal_add_apply, hsmul]
    have hle : (lam : ℝ) * (μ0 / (8 * K))
        ≤ (lam : ℝ) * ν.real (gradRichSet F (μ0 / 2)) :=
      mul_le_mul_of_nonneg_left hνS (by positivity)
    linarith [hle, hsecond]
  exact proposition13 _ F (μ0 / 2) ((lam : ℝ) * (μ0 / (8 * K))) hc hS hF_int hF_nonneg hcover

end Qatlib.Papers.LatentPQCTran26.MainResults.WarmStart
