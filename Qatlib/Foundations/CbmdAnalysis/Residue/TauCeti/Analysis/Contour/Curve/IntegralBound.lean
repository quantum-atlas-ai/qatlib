/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

open MeasureTheory Set

open scoped Interval

namespace TauCeti.Contour

variable {𝕜 E : Type*} [NormedDivisionRing 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module 𝕜 E] [NormSMulClass 𝕜 E]

theorem norm_integral_inv_sub_smul_le {γ : ℝ → 𝕜} {g : ℝ → E} {μ : Measure ℝ} {a b R : ℝ} {w : 𝕜}
    (hg : IntervalIntegrable g μ a b) (hR : ∀ t ∈ Ι a b, ‖γ t‖ ≤ R) (hw : R < ‖w‖) :
    ‖∫ t in a..b, (γ t - w)⁻¹ • g t ∂μ‖ ≤ (∫ t in Ι a b, ‖g t‖ ∂μ) / (‖w‖ - R) := by
  rw [intervalIntegral.norm_integral_eq_norm_integral_uIoc, ← integral_div]
  refine norm_integral_le_of_norm_le (hg.norm.div_const _).def' <|
    ae_restrict_of_forall_mem measurableSet_uIoc fun t ht ↦ ?_
  rw [norm_smul, norm_inv, inv_mul_eq_div]
  gcongr
  linarith [hR t ht, norm_sub_norm_le w (γ t), norm_sub_rev w (γ t)]

end TauCeti.Contour

end
end Qatlib.Foundations.CbmdAnalysis.Residue
