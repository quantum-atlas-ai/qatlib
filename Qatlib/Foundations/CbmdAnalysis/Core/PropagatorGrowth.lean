/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.BesselMixture

/-!
# Exponential growth bounds for wave and Bessel series

Termwise comparison with the hyperbolic cosine series bounds the wave and Bessel propagators in
a complex normed algebra with unit norm. Both obey the exponential estimate `exp (‖t‖ * sqrt
‖A‖)`.

These bounds require no positivity condition on `A` and provide general growth control for the
special-function contour constructions of [WangEtAl2026].

## Main statements

* `wavePropagator_norm_le_exp`: bounds the wave propagator for complex time.
* `besselPropagator_norm_le_exp`: gives the same exponential bound for the Bessel propagator.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
noncomputable section
namespace CBMD
open MeasureTheory

/-- For nonnegative real `x`, `cosh x ≤ exp x`. -/
private theorem cosh_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    Real.cosh x ≤ Real.exp x := by
  rw [Real.cosh_eq]
  have h := Real.exp_le_exp.mpr (show -x ≤ x by linarith)
  linarith

section BanachAlgebra
variable {E : Type*} [NormedRing E] [NormedAlgebra ℂ E] [CompleteSpace E] [NormOneClass E]

omit [NormedAlgebra ℂ E] [CompleteSpace E] [NormOneClass E] in

/-- If each term has norm at most `r ^ (2 * n) / (2 * n)!`, the norm of the total sum is at most
`cosh r`. -/
private theorem norm_tsum_le_cosh (f : ℕ → E) (r : ℝ)
    (hf : ∀ n, ‖f n‖ ≤ r ^ (2 * n) / ((2 * n).factorial : ℝ)) :
    ‖∑' n, f n‖ ≤ Real.cosh r := by
  have hs := (Real.hasSum_cosh r).summable
  have hn : Summable (fun n => ‖f n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hf hs
  exact (norm_tsum_le_tsum_norm hn).trans
    ((hn.tsum_le_tsum hf hs).trans_eq (Real.hasSum_cosh r).tsum_eq)

omit [CompleteSpace E] in

/-- The wave propagator norm is at most `exp (‖t‖ * sqrt ‖A‖)` for every algebra element and
complex time. -/
theorem wavePropagator_norm_le_exp (A : E) (t : ℂ) :
    ‖wavePropagator A t‖ ≤ Real.exp (‖t‖ * Real.sqrt ‖A‖) := by
  apply le_trans (norm_tsum_le_cosh _ (‖t‖ * Real.sqrt ‖A‖) ?_)
    (cosh_le_exp_of_nonneg (by positivity))
  intro n
  rw [norm_smul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ ((2 * n).factorial : ℝ)⁻¹ * ‖-(t ^ 2) • A‖ ^ n :=
      mul_le_mul_of_nonneg_left (norm_pow_le _ _) (by positivity)
    _ = (‖t‖ * Real.sqrt ‖A‖) ^ (2 * n) / ((2 * n).factorial : ℝ) := by
      rw [norm_smul, norm_neg, norm_pow, pow_mul, mul_pow, mul_pow,
        Real.sq_sqrt (norm_nonneg A), div_eq_mul_inv]
      ring

/-- The Bessel propagator norm is at most `exp (‖t‖ * sqrt ‖A‖)` for every algebra element and
complex time. -/
theorem besselPropagator_norm_le_exp (A : E) (t : ℂ) :
    ‖besselPropagator A t‖ ≤ Real.exp (‖t‖ * Real.sqrt ‖A‖) := by
  rw [besselPropagator_wave_mixture, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos Real.pi_pos]
  have hB := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := Real.pi) (C := Real.exp (‖t‖ * Real.sqrt ‖A‖))
    (f := fun θ => wavePropagator A (t * (Real.sin θ : ℂ))) (fun θ _ => by
      apply (wavePropagator_norm_le_exp A _).trans
      apply Real.exp_le_exp.mpr
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        ((mul_le_mul_of_nonneg_left (Real.abs_sin_le_one θ) (norm_nonneg t)).trans_eq
          (mul_one _)) (Real.sqrt_nonneg _))
  have hb : ‖∫ θ in (0 : ℝ)..Real.pi, wavePropagator A (t * (Real.sin θ : ℂ))‖ ≤
      Real.pi * Real.exp (‖t‖ * Real.sqrt ‖A‖) := by
    simpa only [sub_zero, abs_of_pos Real.pi_pos, mul_comm] using hB
  calc
    _ ≤ Real.pi⁻¹ * (Real.pi * Real.exp (‖t‖ * Real.sqrt ‖A‖)) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr Real.pi_pos.le)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ Real.pi_ne_zero, one_mul]

end BanachAlgebra
end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
