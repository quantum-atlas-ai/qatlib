/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.WaveAngularGrowth
import Qatlib.Foundations.CbmdAnalysis.Core.AiryMixture

/-!
# Angular growth of Bessel and Airy propagators

`waveAngularRate` combines the imaginary part of a complex parameter with a perturbation term
involving the inverse square root of `H`. It is nonnegative for all matrices and parameters.

When `H` is positive definite, this rate controls the Bessel and Airy propagators of `L + r² H`
for nonzero `r` and nonnegative real time. These bounds support the special-function contour
estimates of [WangEtAl2026].

## Main statements

* `besselPropagator_matrix_angular`: bounds the Bessel propagator using the angular rate.
* `airyPropagator_matrix_angular`: bounds the Airy propagator with its time scale.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
noncomputable section
namespace CBMD
open Complex MeasureTheory Set Filter
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The rate `|r.im| * sqrt ‖H‖ + ‖r‖⁻¹ * ‖Ring.inverse (CFC.sqrt H) * L‖`. -/
def waveAngularRate (L H : Matrix n n ℂ) (r : ℂ) : ℝ :=
  |r.im| * Real.sqrt ‖H‖ + ‖r‖⁻¹ * ‖Ring.inverse (CFC.sqrt H) * L‖

/-- The angular growth rate is nonnegative for all matrices and complex parameters. -/
theorem waveAngularRate_nonneg (L H : Matrix n n ℂ) (r : ℂ) : 0 ≤ waveAngularRate L H r := by
  unfold waveAngularRate
  positivity

/-- For positive definite `H`, nonzero `r`, and `t ≥ 0`, the Bessel propagator of `L + r² H` has
norm at most `exp (t * waveAngularRate L H r)`. -/
theorem besselPropagator_matrix_angular (L H : Matrix n n ℂ) (hH : H.PosDef)
    (r : ℂ) (hr : r ≠ 0) (t : ℝ) (ht : 0 ≤ t) :
    ‖besselPropagator (L + r ^ 2 • H) (t : ℂ)‖ ≤ Real.exp (t * waveAngularRate L H r) := by
  rw [besselPropagator_wave_mixture, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos Real.pi_pos]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := Real.pi) (C := Real.exp (t * waveAngularRate L H r))
    (f := fun θ => wavePropagator (L + r ^ 2 • H) ((t : ℂ) * (Real.sin θ : ℂ)))
    (fun θ hθ => by
      (try dsimp only)
      have hθ'' : θ ∈ Ioc (0 : ℝ) Real.pi := by simpa only [uIoc_of_le Real.pi_pos.le] using! hθ
      have hθ' : θ ∈ Icc (0 : ℝ) Real.pi := ⟨hθ''.1.le, hθ''.2⟩
      rw [← Complex.ofReal_mul]
      apply (wavePropagator_matrix_angular L H hH r hr (t * Real.sin θ)
        (mul_nonneg ht (Real.sin_nonneg_of_mem_Icc hθ'))).trans
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right
        ((mul_le_mul_of_nonneg_left (Real.sin_le_one θ) ht).trans_eq (mul_one t))
        (waveAngularRate_nonneg L H r))
  have hi' : ‖∫ θ in (0 : ℝ)..Real.pi,
      wavePropagator (L + r ^ 2 • H) ((t : ℂ) * (Real.sin θ : ℂ))‖ ≤
      Real.pi * Real.exp (t * waveAngularRate L H r) := by
    simpa only [sub_zero, abs_of_pos Real.pi_pos, mul_comm] using! hi
  calc
    _ ≤ Real.pi⁻¹ * (Real.pi * Real.exp (t * waveAngularRate L H r)) :=
      mul_le_mul_of_nonneg_left hi' (inv_nonneg.mpr Real.pi_pos.le)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ Real.pi_ne_zero, one_mul]

/-- For positive definite `H`, nonzero `r`, and `t ≥ 0`, the Airy propagator of `L + r² H` has
norm at most `exp (airyTimeScale t * waveAngularRate L H r)`. -/
theorem airyPropagator_matrix_angular (L H : Matrix n n ℂ) (hH : H.PosDef)
    (r : ℂ) (hr : r ≠ 0) (t : ℝ) (ht : 0 ≤ t) :
    ‖airyPropagator (L + r ^ 2 • H) (t : ℂ)‖ ≤
      Real.exp (airyTimeScale t * waveAngularRate L H r) := by
  rw [airyPropagator_wave_mixture _ t ht]
  have hmem : ∀ᵐ u : ℝ ∂airyMixMeasure, u ∈ Ioo (0 : ℝ) 1 :=
      Qatlib.Foundations.CbmdAnalysis.Core.CBMD.betaMeasure_ae_mem
  have hi := norm_integral_le_of_norm_le_const (μ := airyMixMeasure)
    (C := Real.exp (airyTimeScale t * waveAngularRate L H r))
    (f := fun u : ℝ => wavePropagator (L + r ^ 2 • H)
      ((airyTimeScale t : ℂ) * (Real.sqrt u : ℂ))) (by
        filter_upwards [hmem] with u hu
        rw [← Complex.ofReal_mul]
        apply (wavePropagator_matrix_angular L H hH r hr (airyTimeScale t * Real.sqrt u)
          (mul_nonneg (airyTimeScale_nonneg ht) (Real.sqrt_nonneg u))).trans
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right
          ((mul_le_mul_of_nonneg_left (Real.sqrt_le_one.mpr hu.2.le)
            (airyTimeScale_nonneg ht)).trans_eq (mul_one _))
          (waveAngularRate_nonneg L H r))
  simpa using! hi

end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
