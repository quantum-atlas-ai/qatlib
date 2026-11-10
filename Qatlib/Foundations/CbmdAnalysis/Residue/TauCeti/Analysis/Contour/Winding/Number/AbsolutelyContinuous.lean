/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Winding.Number.Basic
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

open MeasureTheory Set

namespace TauCeti.Contour

theorem _root_.Qatlib.Foundations.CbmdAnalysis.Residue.AbsolutelyContinuousOnInterval.intervalIntegrable_inv_sub_mul_deriv
    {γ : ℝ → ℂ} {a b : ℝ} {z : ℂ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hz : z ∉ γ '' uIcc a b) :
    IntervalIntegrable (fun t ↦ (γ t - z)⁻¹ * deriv γ t) volume a b := by
  exact TauCeti.Contour.intervalIntegrable_inv_sub_mul_deriv hγ.continuousOn
    (fun t ht htz ↦ hz ⟨t, ht, htz⟩) (AbsolutelyContinuousOnInterval.intervalIntegrable_deriv_of_finiteDimensional hγ)

theorem _root_.Qatlib.Foundations.CbmdAnalysis.Residue.AbsolutelyContinuousOnInterval.windingNumber_eq_integral
    {γ : ℝ → ℂ} {a b : ℝ} {z : ℂ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hz : z ∉ γ '' uIcc a b) :
    windingNumber γ a b z = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      ∫ t in a..b, (γ t - z)⁻¹ * deriv γ t :=
  windingNumber_eq_integral_of_avoidance hγ.continuousOn
    (fun t ht htz ↦ hz ⟨t, ht, htz⟩)
    (AbsolutelyContinuousOnInterval.intervalIntegrable_inv_sub_mul_deriv hγ hz)

end TauCeti.Contour

end
end Qatlib.Foundations.CbmdAnalysis.Residue
