/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.KernelFiniteCircle
import Qatlib.Foundations.CbmdAnalysis.Core.KernelCircleBounds
import Qatlib.Foundations.CbmdAnalysis.Core.DysonKernel
import Qatlib.Foundations.CbmdAnalysis.Core.DysonPiecewiseInput
import Mathlib.Order.Filter.AtTopBot.Interval

/-!
# The integer sampling series identity

Finite symmetric sums of weighted real samples converge to their absolutely convergent integer
series. Passing to the limit in the finite circle identity gives
`integer_kernel_series_identity`, which expresses the target `U (-i)` as that series minus the
auxiliary correction.

For an entire `U` satisfying the half-plane exponential growth bound, the prescribed finite
sampling parameters then give error at most `δ`. This establishes the analytic sampling step of
contour-based matrix decomposition [WangEtAl2026].

## Main statements

* `integer_kernel_series_identity`: expresses the target through real samples and auxiliary
  residues.
* `integerLCU_target_error_le`: bounds the finite target approximation.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace CBMD
open Complex Metric Set Filter MeasureTheory
open scoped Topology BigOperators Matrix.Norms.L2Operator ComplexOrder

section Banach
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- For `a ≥ 1` and `U` contractive on the real axis, the symmetric finite LCU sums converge to
the infinite weighted integer sample sum. -/
theorem integerLCUSum_tendsto (m : ℕ) {a : ℝ} (ha : 1 ≤ a) (U : ℂ → E)
    (hUreal : ∀ x : ℝ, ‖U (x : ℂ)‖ ≤ 1) :
    Tendsto (fun n : ℕ => integerLCUSum m a n U) atTop
      (𝓝 (∑' k : ℤ, integerSample m a U k)) := by
  exact ((integerSample_norm_summable m ha U hUreal).of_norm.hasSum).comp Finset.tendsto_Icc_neg

/-- For `a ≥ 1`, `ρ ≤ 2πa`, and an entire `U` with the stated half-plane growth bound, `U (-i)`
equals the infinite weighted sample sum minus the auxiliary correction [WangEtAl2026]. -/
theorem integer_kernel_series_identity (m : ℕ) {a ρ : ℝ} (ha : 1 ≤ a)
    (hρ : ρ ≤ 2 * Real.pi * a) (U : ℂ → E) (hUanalytic : Differentiable ℂ U)
    (hU : ∀ z, ‖U z‖ ≤ Real.exp (max z.im 0 * ρ)) :
    U (-Complex.I) = (∑' k : ℤ, integerSample m a U k) - integerAuxiliaryCorrection m a U := by
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hreal (x : ℝ) : ‖U (x : ℂ)‖ ≤ 1 := by simpa using hU (x : ℂ)
  have hs := integerLCUSum_tendsto m ha U hreal
  have hc := integerContour_circle_tendsto_zero m ha0 hρ U hU
  have he : (fun n : ℕ => (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      ∮ z in C(0, halfGridRadius a n), integerContourIntegrand m a U z) =ᶠ[atTop]
      (fun n => U (-Complex.I) - integerLCUSum m a n U + integerAuxiliaryCorrection m a U) := by
    filter_upwards [(halfGridRadius_tendsto ha0).eventually_gt_atTop ((m : ℝ) + 2)] with n hn
    exact integerContour_circle_identity_normalized m ha0 n hn U hUanalytic
  have hr :=
      ((tendsto_const_nhds (x := U (-Complex.I))).sub hs).add_const
      (integerAuxiliaryCorrection m a U)
  have hz : U (-Complex.I) - (∑' k : ℤ, integerSample m a U k) + integerAuxiliaryCorrection m a U = 0 :=
    tendsto_nhds_unique hr (hc.congr' he)
  calc
    U (-Complex.I) = (U (-Complex.I) - (∑' k : ℤ, integerSample m a U k) +
        integerAuxiliaryCorrection m a U) + (∑' k : ℤ, integerSample m a U k) - integerAuxiliaryCorrection m a U := by abel
    _ = _ := by rw [hz, zero_add]

/-- For `0 < δ ≤ 1`, the prescribed order, spacing, and cutoff approximate `U (-i)` within `δ`
whenever `U` is entire and satisfies the stated half-plane exponential growth bound
[WangEtAl2026]. -/
theorem integerLCU_target_error_le (ρ : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (U : ℂ → E) (hUanalytic : Differentiable ℂ U)
    (hU : ∀ z, ‖U z‖ ≤ Real.exp (max z.im 0 * ρ)) :
    let m := kernelOrder (δ / 2)
    let a := kernelSpacing ρ (δ / 2) m
    let K := kernelCutoff a (δ / 2)
    ‖U (-Complex.I) - integerLCUSum m a K U‖ ≤ δ := by
  (try dsimp only)
  apply integerLCU_approximation_of_series_identity ρ hδ hδ1 U
  · intro x
    simpa using hU (x : ℂ)
  · simpa using hU (2 * Complex.I)
  · intro r _
    simpa using hU ((r : ℂ) + Complex.I)
  · apply integer_kernel_series_identity _ (kernelSpacing_ge_one _ _ _)
      (kernelSpacing_growth_le ρ (by positivity) (by linarith) _) U hUanalytic hU

end Banach
end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
