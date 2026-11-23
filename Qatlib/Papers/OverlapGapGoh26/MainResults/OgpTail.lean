/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.OverlapGapGoh26.MainResults.BinaryNoGo

@[expose] public section

/-!
# The exponentially small OGP failure probability

Assumption 2.3 of Goh and Müller (arXiv:2609.35131v1) states an exponential
probability bound for the extended OGP. This file transfers an exponential
bound on the pinned model event to the fixed-step source MF-AOA obstruction.
-/

set_option autoImplicit false

open Filter MeasureTheory ProbabilityTheory
open scoped Topology
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.RawInput
open Qatlib.Papers.OverlapGapGoh26.MainResults

namespace Qatlib.Papers.OverlapGapGoh26.MainResults

/-- An exponentially small failure probability for the model OGP tends to zero. -/
theorem ogp_failure_tendsto {r : ℕ} (μ ν₁ ν₂ : ℝ) {c : ℝ} (hc : 0 < c)
    (h : ∀ᶠ N : ℕ in atTop,
      ((gaussianTensorLaw r N).prod (gaussianTensorLaw r N)).real
        (RawNoGo.modelOgp r N μ ν₁ ν₂)ᶜ ≤ Real.exp (-c * (N : ℝ))) :
    Tendsto (fun N : ℕ => ((gaussianTensorLaw r N).prod (gaussianTensorLaw r N)).real
      (RawNoGo.modelOgp r N μ ν₁ ν₂)ᶜ) atTop (𝓝 0) := by
  have hscale : Tendsto (fun N : ℕ => c * (N : ℝ)) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hc).2 tendsto_natCast_atTop_atTop
  refine squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) h ?_
  simpa only [Function.comp_def, neg_mul] using
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale

/-- The source schedule inherits the conditional fixed-step obstruction from an exponential
failure bound on the model OGP. The event uses the pinned continuous readout and binary optimum. -/
theorem source_mf_nogo_of_ogp_tail {r : ℕ} (hr : Odd r) {T : ℕ} (hT : 0 < T)
    {μ ν₁ ν₂ c : ℝ} (hμ : 0 < μ) (hlo : 0 < ν₁) (hgap : ν₁ < ν₂) (hhi : ν₂ < 1)
    (hc : 0 < c) (h : ∀ᶠ N : ℕ in atTop,
      ((gaussianTensorLaw r N).prod (gaussianTensorLaw r N)).real
        (RawNoGo.modelOgp r N μ ν₁ ν₂)ᶜ ≤ Real.exp (-c * (N : ℝ))) :
    Tendsto (fun N : ℕ => (stdGaussian (Input r N)).real
      (BinaryNoGo.nearBinary (ActualMF.sourceSchedule T) T (μ / 16))) atTop (𝓝 0) :=
  BinaryNoGo.actual_source_mf_nogo hr T hT μ ν₁ ν₂ hμ hlo hgap hhi
    (ogp_failure_tendsto μ ν₁ ν₂ hc h)

end Qatlib.Papers.OverlapGapGoh26.MainResults
