/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.WaveBesselODE
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Bessel propagators as wave mixtures

This module represents `besselPropagator` as the average of wave propagators with sinusoidally
scaled time. Wallis moments identify the integrated coefficients, while the scalar wave formula
gives norm bounds for both propagators on nonnegative scalar inputs. These mixture and
contraction estimates support [WangEtAl2026].

## Main statements

* `besselPropagator_wave_mixture`: the Bessel propagator is the normalized sine-time wave
  integral.
* `wavePropagator_scalar_square`: a scalar square reduces the wave propagator to complex cosine.
* `besselPropagator_scalar_nonneg_norm_le_one`: nonnegative scalar inputs give norm at most one
  at real times.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false

noncomputable section
namespace CBMD
open Complex MeasureTheory Metric Filter
open scoped Topology

/-- The ratio of successive norms of inverse even factorials is `((2 * n + 2) * (2 * n + 1))⁻¹`. -/
private theorem even_factorial_ratio (n : ℕ) :
    ‖(((2 * (n + 1)).factorial : ℂ)⁻¹)‖ / ‖(((2 * n).factorial : ℂ)⁻¹)‖ =
      ((2 * (n : ℝ) + 2) * (2 * (n : ℝ) + 1))⁻¹ := by
  simp only [norm_inv, Complex.norm_natCast]
  have hfact : ((2 * (n + 1)).factorial : ℝ) =
      ((2 * (n : ℝ) + 2) * (2 * (n : ℝ) + 1)) * ((2 * n).factorial : ℝ) := by
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
      Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  rw [hfact]
  have hf : ((2 * n).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (2 * n))
  have h1 : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : 2 * (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp

/-- The ratio of successive norms of inverse even factorials tends to zero. -/
private theorem even_factorial_ratio_tendsto :
    Tendsto (fun n : ℕ => ‖(((2 * n.succ).factorial : ℂ)⁻¹)‖ /
      ‖(((2 * n).factorial : ℂ)⁻¹)‖) atTop (𝓝 0) := by
  simp_rw [Nat.succ_eq_add_one, even_factorial_ratio]
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hm : Tendsto (fun n : ℕ => 2 * (n : ℝ)) atTop atTop :=
    hn.const_mul_atTop (by norm_num)
  have h1 := tendsto_atTop_add_const_right atTop (1 : ℝ) hm
  have h2 := tendsto_atTop_add_const_right atTop (2 : ℝ) hm
  exact tendsto_inv_atTop_zero.comp (h2.atTop_mul_atTop₀ h1)

section BanachAlgebra
variable {E : Type*} [NormedRing E] [NormedAlgebra ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in

/-- The norms of the wave propagator power-series terms are summable for every `A` and complex
time `t`. -/
theorem wave_series_norm_summable (A : E) (t : ℂ) :
    Summable (fun n : ℕ => ‖(((2 * n).factorial : ℂ)⁻¹) • (-(t ^ 2) • A) ^ n‖) := by
  let c : ℕ → ℂ := fun n => ((2 * n).factorial : ℂ)⁻¹
  let p := FormalMultilinearSeries.ofScalars E c
  have hr : p.radius = ⊤ := FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto E c
    (Filter.Eventually.of_forall (fun n => inv_ne_zero
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (2 * n))))) Qatlib.Foundations.CbmdAnalysis.Core.CBMD.even_factorial_ratio_tendsto
  have hm : -(t ^ 2) • A ∈ Metric.eball (0 : E) p.radius := by rw [hr]; exact edist_lt_top _ _
  simpa only [p, c, FormalMultilinearSeries.ofScalars_apply_eq] using p.summable_norm_apply hm

omit [CompleteSpace E] in

/-- Multiplying the `n`th wave-series term by `s ^ (2 * n)` is equivalent to scaling the complex
time by the real number `s`. -/
theorem wave_scaled_term (A : E) (t : ℂ) (s : ℝ) (n : ℕ) :
    s ^ (2 * n) • ((((2 * n).factorial : ℂ)⁻¹) • (-(t ^ 2) • A) ^ n) =
      (((2 * n).factorial : ℂ)⁻¹) • (-((t * (s : ℂ)) ^ 2) • A) ^ n := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rw [show -((t * (s : ℂ)) ^ 2) • A = (s : ℂ) ^ 2 • (-(t ^ 2) • A) by
    rw [smul_smul]; congr 1; ring]
  rw [smul_pow ((s : ℂ) ^ 2) (-(t ^ 2) • A) n]
  simp only [← pow_mul, RCLike.ofReal_pow]
  rw [smul_comm]
  rfl

/-- The integral of `sin θ ^ (2 * n)` on `[0, π]`, divided by `(2 * n)!`, equals `π * (n!)⁻² *
(1 / 4) ^ n`. -/
private theorem bessel_wallismoment (n : ℕ) :
    (∫ θ in (0 : ℝ)..Real.pi, Real.sin θ ^ (2 * n)) *
      (((2 * n).factorial : ℝ)⁻¹) =
      Real.pi * ((n.factorial : ℝ)⁻¹) ^ 2 * (1 / 4 : ℝ) ^ n := by
  rw [integral_sin_pow_even]
  have hp : (∏ i ∈ Finset.range n, (2 * (i : ℝ) + 1) / (2 * i + 2)) *
      (((2 * n).factorial : ℝ)⁻¹) = ((n.factorial : ℝ)⁻¹) ^ 2 * (1 / 4 : ℝ) ^ n := by
    induction n with
    | zero => norm_num
    | succ k ih =>
      rw [Finset.prod_range_succ]
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
        Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ (1 / 4 : ℝ) k]
      have h0 : ((2 * k).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (2 * k))
      have h1 : 2 * (k : ℝ) + 1 ≠ 0 := by positivity
      have h2 : 2 * (k : ℝ) + 1 + 1 ≠ 0 := by positivity
      have hk : (k : ℝ) + 1 ≠ 0 := by positivity
      have hfac : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
      field_simp at ih ⊢
      nlinarith [ih]
  rw [mul_assoc, hp]
  ring

/-- Integrating the sine-weighted `n`th wave-series term over `[0, π]` gives `π` times the
corresponding Bessel-series term. -/
private theorem bessel_integrated_term (A : E) (t : ℂ) (n : ℕ) :
    (∫ θ in (0 : ℝ)..Real.pi, Real.sin θ ^ (2 * n) •
      ((((2 * n).factorial : ℂ)⁻¹) • (-(t ^ 2) • A) ^ n)) =
      Real.pi • (((n.factorial : ℂ)⁻¹) ^ 2 • ((-(t ^ 2) / 4) • A) ^ n) := by
  rw [intervalIntegral.integral_smul_const]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ)]
  have hs : ((-(t ^ 2) / 4) • A) = (1 / 4 : ℂ) • (-(t ^ 2) • A) := by
    rw [smul_smul]
    congr 1
    ring
  rw [hs, smul_pow (1 / 4 : ℂ) (-(t ^ 2) • A) n]
  simp only [smul_smul]
  apply congrArg (fun c : ℂ => c • (-(t ^ 2) • A) ^ n)
  change ((∫ θ in (0 : ℝ)..Real.pi, Real.sin θ ^ (2 * n) : ℝ) : ℂ) *
      (((2 * n).factorial : ℂ)⁻¹) =
    (Real.pi : ℂ) * (((n.factorial : ℂ)⁻¹) ^ 2 * (1 / 4 : ℂ) ^ n)
  have h := congrArg (fun x : ℝ => (x : ℂ)) (bessel_wallismoment n)
  push_cast at h
  simpa only [mul_assoc] using h

/-- The Bessel propagator at complex time `t` equals `1 / π` times the integral of wave
propagators at times `t * sin θ` over `[0, π]`. -/
theorem besselPropagator_wave_mixture (A : E) (t : ℂ) :
    besselPropagator A t = (Real.pi⁻¹) •
      (∫ θ in (0 : ℝ)..Real.pi, wavePropagator A (t * (Real.sin θ : ℂ))) := by
  let F : ℕ → ℝ → E := fun n θ => Real.sin θ ^ (2 * n) •
    ((((2 * n).factorial : ℂ)⁻¹) • (-(t ^ 2) • A) ^ n)
  let b : ℕ → ℝ := fun n => ‖(((2 * n).factorial : ℂ)⁻¹) • (-(t ^ 2) • A) ^ n‖
  have hb : Summable b := wave_series_norm_summable A t
  have hsum : HasSum (fun n => ∫ θ in (0 : ℝ)..Real.pi, F n θ)
      (∫ θ in (0 : ℝ)..Real.pi, wavePropagator A (t * (Real.sin θ : ℂ))) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence (fun n _ => b n)
    · intro n
      exact ((Real.continuous_sin.pow _).smul continuous_const).aestronglyMeasurable
    · intro n
      apply Filter.Eventually.of_forall
      intro θ hθ
      change ‖Real.sin θ ^ (2 * n) • _‖ ≤ b n
      rw [norm_smul, Real.norm_eq_abs, abs_pow]
      exact (mul_le_mul_of_nonneg_right
        (pow_le_one₀ (abs_nonneg _) (Real.abs_sin_le_one θ)) (norm_nonneg _)).trans_eq
          (one_mul _)
    · exact Filter.Eventually.of_forall (fun _ _ => hb)
    · exact intervalIntegrable_const
    · apply Filter.Eventually.of_forall
      intro θ hθ
      have h := (wave_series_summable A (t * (Real.sin θ : ℂ))).hasSum
      simpa only [F, wave_scaled_term] using! h
  have ht : HasSum (fun n => ∫ θ in (0 : ℝ)..Real.pi, F n θ)
      (Real.pi • besselPropagator A t) := by
    simpa only [F, bessel_integrated_term] using!
      (bessel_series_summable A t).hasSum.const_smul Real.pi
  rw [hsum.unique ht, smul_smul, inv_mul_cancel₀ Real.pi_ne_zero, one_smul]

end BanachAlgebra

/-- The scalar wave propagator at argument `z ^ 2` and time `t` equals `cos (t * z)`. -/
theorem wavePropagator_scalar_square (z t : ℂ) :
    wavePropagator (z ^ 2) t = Complex.cos (t * z) := by
  rw [wavePropagator, Complex.cos_eq_tsum]
  apply tsum_congr
  intro n
  simp only [smul_eq_mul]
  have hs : -(t ^ 2) * z ^ 2 = -(t * z) ^ 2 := by ring
  rw [hs, neg_pow, ← pow_mul]
  simp only [div_eq_mul_inv]
  ring

/-- For a nonnegative real scalar input, the wave propagator has norm at most one at every real
time. -/
theorem wavePropagator_scalar_nonneg_norm_le_one (x t : ℝ) (hx : 0 ≤ x) :
    ‖wavePropagator (x : ℂ) (t : ℂ)‖ ≤ 1 := by
  have hx' : (x : ℂ) = (Real.sqrt x : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hx]
  rw [hx', wavePropagator_scalar_square, ← Complex.ofReal_mul,
    ← Complex.ofReal_cos, Complex.norm_real, Real.norm_eq_abs]
  exact Real.abs_cos_le_one _

/-- For a nonnegative real scalar input, the Bessel propagator has norm at most one at every
real time. -/
theorem besselPropagator_scalar_nonneg_norm_le_one (x t : ℝ) (hx : 0 ≤ x) :
    ‖besselPropagator (x : ℂ) (t : ℂ)‖ ≤ 1 := by
  rw [besselPropagator_wave_mixture, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos Real.pi_pos]
  have hb : ‖∫ θ in (0 : ℝ)..Real.pi,
      wavePropagator (x : ℂ) ((t : ℂ) * (Real.sin θ : ℂ))‖ ≤ Real.pi := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := Real.pi) (C := 1)
      (f := fun θ => wavePropagator (x : ℂ) ((t : ℂ) * (Real.sin θ : ℂ)))
      (fun θ _ => by
        (try dsimp only)
        rw [← Complex.ofReal_mul]
        exact wavePropagator_scalar_nonneg_norm_le_one x (t * Real.sin θ) hx)
    simpa [abs_of_pos Real.pi_pos] using h
  calc
    Real.pi⁻¹ * _ ≤ Real.pi⁻¹ * Real.pi :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr Real.pi_pos.le)
    _ = 1 := inv_mul_cancel₀ Real.pi_ne_zero

end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
