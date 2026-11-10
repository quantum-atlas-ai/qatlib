/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LatentPQCTran26.MainResults.Coverage
import Qatlib.Papers.LatentPQCTran26.MainResults.Trainability
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace Qatlib.Papers.LatentPQCTran26.MainResults.WarmStart

open Qatlib.Papers.LatentPQCTran26.MainResults.Overlap
open Qatlib.Papers.LatentPQCTran26.MainResults.Trainability

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
