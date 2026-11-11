/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhRule
import Qatlib.Papers.CommutLCHS26.QuadratureCmp.Moments

/-!
# Actual moments of sinh quadrature rules

This module defines `moment` using the actual Jacobian-weighted coefficients and physical nodes
of the finite sinh rule in [AftabAnTrivisa2026]. The coefficient norm at zero gives a lower
bound for the zeroth moment through its central sample.

## Main statements

* `norm_coefficient_zero`: the exact central coefficient norm.
* `central_le_moment`: the central contribution is a lower bound for the zeroth moment.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhMoments
open Complex Matrix Set Filter MeasureTheory
open scoped Topology BigOperators Matrix.Norms.L2Operator ComplexOrder
open Qatlib.Papers.CommutLCHS26.MainResults.KernelStrip
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhRule
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.TailBudget
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.Trapezoid (cutoff)
set_option warningAsError false
variable {ι : Type} [Fintype ι] [DecidableEq ι]
local instance : ContinuousENorm (Matrix ι ι ℂ) :=
  SeminormedAddGroup.toESeminormedAddMonoid.toContinuousENorm

/-- The finite sinh quadrature moment formed from the norms of the Jacobian-weighted
coefficients and the absolute physical node values to the power `ν`. -/
def moment (n : ℕ) (b c d ν η h : ℝ) (N : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc (-(N : ℤ)) N,
    ‖((h * η * Real.cosh (h * (q : ℝ)) : ℝ) : ℂ) *
      coefficient n b c d ((η * Real.sinh (h * (q : ℝ)) : ℝ) : ℂ)‖ *
        |η * Real.sinh (h * (q : ℝ))| ^ ν

/-- For positive `b`, the coefficient norm at zero is `kernelScale / bⁿ`. -/
theorem norm_coefficient_zero (n : ℕ) (b c d : ℝ) (hb : 0 < b) :
    ‖coefficient n b c d 0‖ =
      Qatlib.Papers.CommutLCHS26.QuadratureCmp.Moments.kernelScale n b c d / b ^ n := by
  rw [norm_coefficient n b c d hb]
  simp [Qatlib.Papers.CommutLCHS26.QuadratureCmp.Moments.kernelScale,
    Real.norm_of_nonneg hb.le, neg_div, sub_eq_add_neg]

/-- For nonnegative sinh scale and mesh step, the zeroth sinh moment is at least its central
contribution `h * η * kernelScale / bⁿ`. -/
theorem central_le_moment (n : ℕ) (b c d η h : ℝ) (hb : 0 < b) (hη : 0 ≤ η)
    (hh : 0 ≤ h) (N : ℕ) :
    h * η * (Qatlib.Papers.CommutLCHS26.QuadratureCmp.Moments.kernelScale n b c d / b ^ n) ≤
      moment n b c d 0 η h N := by
  have hm : (0 : ℤ) ∈ Finset.Icc (-(N : ℤ)) N := by simp
  let f : ℤ → ℝ := fun q =>
    ‖((h * η * Real.cosh (h * (q : ℝ)) : ℝ) : ℂ) *
      coefficient n b c d ((η * Real.sinh (h * (q : ℝ)) : ℝ) : ℂ)‖ *
        |η * Real.sinh (h * (q : ℝ))| ^ (0 : ℝ)
  have hn (q : ℤ) : 0 ≤ f q := by
    dsimp [f]
    exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (abs_nonneg _) _)
  have hs : f 0 ≤ ∑ q ∈ Finset.Icc (-(N : ℤ)) N, f q :=
    Finset.single_le_sum (fun q _ => hn q) hm
  change _ ≤ ∑ q ∈ Finset.Icc (-(N : ℤ)) N, _
  convert! hs using 1
  dsimp [f]
  simp only [Int.cast_zero, mul_zero, Real.cosh_zero, mul_one, Real.sinh_zero,
    Complex.ofReal_zero, Real.rpow_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hh, abs_of_nonneg hη, norm_coefficient_zero n b c d hb]

end Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhMoments
