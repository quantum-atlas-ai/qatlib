/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Qatlib Contributors

Adapted from https://github.com/TauCetiProject/TauCeti@3780371c
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Winding.Number.Basic
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Integral formula for absolutely continuous winding numbers

Shows that an absolutely continuous curve avoiding a point has an interval-integrable
logarithmic derivative. Its ordinary integral, normalized by `2πi`, computes `windingNumber`.

This bridges the principal-value definition and ordinary contour integrals in the framework
associated with [WangEtAl2026].

## Main statements

* `AbsolutelyContinuousOnInterval.intervalIntegrable_inv_sub_mul_deriv`: The logarithmic
  derivative of an absolutely continuous curve about a point outside its image is interval
  integrable.
* `AbsolutelyContinuousOnInterval.windingNumber_eq_integral`: For an absolutely continuous curve
  avoiding `z`, the winding number is its logarithmic derivative integral divided by `2πi`.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

open MeasureTheory Set

namespace TauCeti.Contour

/-- The logarithmic derivative of an absolutely continuous curve about a point outside its image
is interval integrable. -/
theorem _root_.AbsolutelyContinuousOnInterval.intervalIntegrable_inv_sub_mul_deriv
    {γ : ℝ → ℂ} {a b : ℝ} {z : ℂ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hz : z ∉ γ '' uIcc a b) :
    IntervalIntegrable (fun t ↦ (γ t - z)⁻¹ * deriv γ t) volume a b := by
  exact TauCeti.Contour.intervalIntegrable_inv_sub_mul_deriv hγ.continuousOn
    (fun t ht htz ↦ hz ⟨t, ht, htz⟩) (AbsolutelyContinuousOnInterval.intervalIntegrable_deriv_of_finiteDimensional hγ)

/-- For an absolutely continuous curve avoiding `z`, the winding number is its logarithmic
derivative integral divided by `2πi`. -/
theorem _root_.AbsolutelyContinuousOnInterval.windingNumber_eq_integral
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
