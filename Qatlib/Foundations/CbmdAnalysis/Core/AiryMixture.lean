/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.PositivePropagators
import Qatlib.Foundations.CbmdAnalysis.Core.PropagatorGrowth
import Mathlib.Probability.Distributions.Beta
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
noncomputable section
namespace CBMD
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology

private theorem betaPDFReal_nonneg {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (x : ℝ) :
    0 ≤ betaPDFReal α β x := by
  by_cases hx : 0 < x ∧ x < 1
  · exact (betaPDFReal_pos hx.1 hx.2 hα hβ).le
  · simp [betaPDFReal, hx]

private theorem beta_integral_eq_density {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (f : ℝ → E) :
    (∫ x, f x ∂betaMeasure α β) = ∫ x, betaPDFReal α β x • f x := by
  change (∫ x, f x ∂volume.withDensity (fun x => ENNReal.ofReal (betaPDFReal α β x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    ((measurable_betaPDFReal α β).ennreal_ofReal) (by simp)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  (try dsimp only)
  rw [ENNReal.toReal_ofReal (betaPDFReal_nonneg hα hβ x)]

private theorem integral_betaPDFReal {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    (∫ x, betaPDFReal α β x) = 1 := by
  letI := isProbabilityMeasureBeta hα hβ
  have h : (∫ _x : ℝ, (1 : ℝ) ∂betaMeasure α β) = 1 := by simp
  rw [beta_integral_eq_density hα hβ] at h
  simpa only [smul_eq_mul, mul_one] using! h

private theorem beta_moment_density {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (n : ℕ) (x : ℝ) :
    betaPDFReal α β x * x ^ n =
      (beta (α + n) β / beta α β) * betaPDFReal (α + n) β x := by
  by_cases hx : 0 < x ∧ x < 1
  · simp only [betaPDFReal, if_pos hx]
    rw [show α + (n : ℝ) - 1 = (α - 1) + n by ring,
      Real.rpow_add hx.1, Real.rpow_natCast]
    have h1 := ne_of_gt (beta_pos hα hβ)
    have h2 := ne_of_gt (beta_pos (by positivity : 0 < α + n) hβ)
    field_simp
  · simp [betaPDFReal, hx]

private theorem betaMeasure_moment {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (n : ℕ) :
    (∫ x : ℝ, x ^ n ∂betaMeasure α β) = beta (α + n) β / beta α β := by
  rw [beta_integral_eq_density hα hβ]
  simp_rw [smul_eq_mul, beta_moment_density hα hβ n]
  rw [integral_const_mul, integral_betaPDFReal (by positivity : 0 < α + n) hβ, mul_one]

theorem betaMeasure_ae_mem {α β : ℝ} :
    ∀ᵐ x : ℝ ∂betaMeasure α β, x ∈ Ioo (0 : ℝ) 1 := by
  change ∀ᵐ x : ℝ ∂volume.withDensity (fun x => ENNReal.ofReal (betaPDFReal α β x)), x ∈ Ioo 0 1
  rw [ae_withDensity_iff ((measurable_betaPDFReal α β).ennreal_ofReal)]
  apply Eventually.of_forall
  intro x hx
  by_contra h
  change ¬(0 < x ∧ x < 1) at h
  exact hx (by simp [betaPDFReal, h])

private theorem beta_step {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    beta (α + 1) β = α / (α + β) * beta α β := by
  unfold beta
  rw [Real.Gamma_add_one hα.ne', show α + 1 + β = (α + β) + 1 by ring,
    Real.Gamma_add_one (add_pos hα hβ).ne']
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

def airyMixMeasure : Measure ℝ := betaMeasure (1 / 2) (1 / 6)

instance airyMixMeasure_probability : IsProbabilityMeasure airyMixMeasure :=
  isProbabilityMeasureBeta (by norm_num) (by norm_num)

private def airyBetaMoment (n : ℕ) : ℝ :=
  beta (1 / 2 + n) (1 / 6) / beta (1 / 2) (1 / 6)

private theorem airyBetaMoment_zero : airyBetaMoment 0 = 1 := by
  simp only [airyBetaMoment, Nat.cast_zero, add_zero]
  exact div_self (ne_of_gt (beta_pos (by norm_num) (by norm_num)))

private theorem airyBetaMoment_step (n : ℕ) :
    airyBetaMoment (n + 1) =
      ((n : ℝ) + 1 / 2) / ((n : ℝ) + 2 / 3) * airyBetaMoment n := by
  unfold airyBetaMoment
  rw [Nat.cast_add, Nat.cast_one, ← add_assoc,
    beta_step (by positivity : 0 < (1 / 2 : ℝ) + n) (by norm_num : (0 : ℝ) < 1 / 6)]
  rw [show (1 / 2 : ℝ) + n = n + 1 / 2 by ring,
    show (n : ℝ) + 1 / 2 + 1 / 6 = n + 2 / 3 by ring]
  ring

private theorem airyBetaMoment_coefficient (n : ℕ) :
    airyBetaMoment n * (((2 * n).factorial : ℝ)⁻¹) * (4 / 9 : ℝ) ^ n =
      airySeriesCoefficient n := by
  induction n with
  | zero => simp [airyBetaMoment_zero]
  | succ k ih =>
    rw [airySeriesCoefficient_step, ← ih,
      airyBetaMoment_step, pow_succ (4 / 9 : ℝ) k,
      show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
      Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    have h0 : ((2 * k).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (2 * k))
    have h1 : 2 * (k : ℝ) + 1 ≠ 0 := by positivity
    have h2 : 2 * (k : ℝ) + 1 + 1 ≠ 0 := by positivity
    have h3 : 3 * (k : ℝ) + 3 ≠ 0 := by positivity
    have h4 : 3 * (k : ℝ) + 2 ≠ 0 := by positivity
    have h5 : (k : ℝ) + 2 / 3 ≠ 0 := by positivity
    field_simp
    ring

theorem airyMixMeasure_moment_coefficient (n : ℕ) :
    (∫ u : ℝ, u ^ n ∂airyMixMeasure) * (((2 * n).factorial : ℝ)⁻¹) *
      (4 / 9 : ℝ) ^ n = airySeriesCoefficient n := by
  rw [airyMixMeasure, betaMeasure_moment (by norm_num) (by norm_num)]
  exact airyBetaMoment_coefficient n

def airyTimeScale (t : ℝ) : ℝ := (2 / 3) * t * Real.sqrt t

theorem airyTimeScale_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ airyTimeScale t := by
  unfold airyTimeScale
  positivity

theorem airyTimeScale_sq {t : ℝ} (ht : 0 ≤ t) :
    airyTimeScale t ^ 2 = (4 / 9) * t ^ 3 := by
  unfold airyTimeScale
  rw [mul_pow, Real.sq_sqrt ht]
  ring

section BanachAlgebra
variable {E : Type*} [NormedRing E] [NormedAlgebra ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in

private theorem airy_mixture_term (A : E) (t u : ℝ) (hu : 0 ≤ u) (n : ℕ) :
    u ^ n • ((((2 * n).factorial : ℂ)⁻¹) • (-((airyTimeScale t : ℂ) ^ 2) • A) ^ n) =
      (((2 * n).factorial : ℂ)⁻¹) •
        (-(((airyTimeScale t : ℂ) * (Real.sqrt u : ℂ)) ^ 2) • A) ^ n := by
  have h : Real.sqrt u ^ (2 * n) = u ^ n := by
    rw [pow_mul, Real.sq_sqrt hu]
  rw [← h]
  exact Qatlib.Foundations.CbmdAnalysis.Core.CBMD.wave_scaled_term A (airyTimeScale t : ℂ)
      (Real.sqrt u) n

private theorem airy_integrated_term (A : E) (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    (∫ u : ℝ, u ^ n • ((((2 * n).factorial : ℂ)⁻¹) •
      (-((airyTimeScale t : ℂ) ^ 2) • A) ^ n) ∂airyMixMeasure) =
      (airySeriesCoefficient n : ℂ) • (-((t : ℂ) ^ 3) • A) ^ n := by
  rw [integral_smul_const, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  have hs : -((airyTimeScale t : ℂ) ^ 2) • A =
      (4 / 9 : ℂ) • (-((t : ℂ) ^ 3) • A) := by
    rw [← Complex.ofReal_pow, airyTimeScale_sq ht]
    push_cast
    rw [smul_smul]
    congr 1
    ring
  rw [hs, smul_pow (4 / 9 : ℂ) (-((t : ℂ) ^ 3) • A) n]
  simp only [smul_smul]
  apply congrArg (fun c : ℂ => c • (-((t : ℂ) ^ 3) • A) ^ n)
  have h := congrArg (fun x : ℝ => (x : ℂ)) (airyMixMeasure_moment_coefficient n)
  push_cast at h
  simpa only [mul_assoc] using! h

theorem airyPropagator_wave_mixture (A : E) (t : ℝ) (ht : 0 ≤ t) :
    airyPropagator A (t : ℂ) =
      ∫ u : ℝ, wavePropagator A
        ((airyTimeScale t : ℂ) * (Real.sqrt u : ℂ)) ∂airyMixMeasure := by
  let F : ℕ → ℝ → E := fun n u => u ^ n •
    ((((2 * n).factorial : ℂ)⁻¹) • (-((airyTimeScale t : ℂ) ^ 2) • A) ^ n)
  let b : ℕ → ℝ := fun n =>
    ‖(((2 * n).factorial : ℂ)⁻¹) • (-((airyTimeScale t : ℂ) ^ 2) • A) ^ n‖
  have hb : Summable b :=
      Qatlib.Foundations.CbmdAnalysis.Core.CBMD.wave_series_norm_summable A (airyTimeScale t : ℂ)
  have hmem : ∀ᵐ u : ℝ ∂airyMixMeasure, u ∈ Ioo (0 : ℝ) 1 := betaMeasure_ae_mem
  have hsum : HasSum (fun n => ∫ u : ℝ, F n u ∂airyMixMeasure)
      (∫ u : ℝ, wavePropagator A
        ((airyTimeScale t : ℂ) * (Real.sqrt u : ℂ)) ∂airyMixMeasure) := by
    apply MeasureTheory.hasSum_integral_of_dominated_convergence (fun n _ => b n)
    · intro n
      exact ((continuous_id.pow _).smul continuous_const).aestronglyMeasurable
    · intro n
      filter_upwards [hmem] with u hu
      change ‖u ^ n • _‖ ≤ b n
      rw [norm_smul, Real.norm_eq_abs, abs_pow, abs_of_pos hu.1]
      exact (mul_le_mul_of_nonneg_right
        (pow_le_one₀ hu.1.le hu.2.le) (norm_nonneg _)).trans_eq (one_mul _)
    · exact Eventually.of_forall (fun _ => hb)
    · exact integrable_const _
    · filter_upwards [hmem] with u hu
      have h := (wave_series_summable A
        ((airyTimeScale t : ℂ) * (Real.sqrt u : ℂ))).hasSum
      simpa only [F, airy_mixture_term A t u hu.1.le] using! h
  have hactual : HasSum (fun n => ∫ u : ℝ, F n u ∂airyMixMeasure)
      (airyPropagator A (t : ℂ)) := by
    simpa only [F, airy_integrated_term A t ht] using! (airy_series_summable A (t : ℂ)).hasSum
  exact hactual.unique hsum

end BanachAlgebra

theorem airyPropagator_scalar_nonneg_norm_le_one (x t : ℝ) (hx : 0 ≤ x) (ht : 0 ≤ t) :
    ‖airyPropagator (x : ℂ) (t : ℂ)‖ ≤ 1 := by
  rw [airyPropagator_wave_mixture _ t ht]
  have h := norm_integral_le_of_norm_le_const (μ := airyMixMeasure) (C := 1)
    (f := fun u : ℝ => wavePropagator (x : ℂ)
      ((airyTimeScale t : ℂ) * (Real.sqrt u : ℂ))) (Eventually.of_forall (fun u => by
        (try dsimp only)
        rw [← Complex.ofReal_mul]
        exact wavePropagator_scalar_nonneg_norm_le_one x _ hx))
  simpa using! h

open scoped Matrix.Norms.L2Operator ComplexOrder in

theorem airyPropagator_posSemidef_norm_le_one {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.PosSemidef) (t : ℝ) (ht : 0 ≤ t) :
    ‖airyPropagator A (t : ℂ)‖ ≤ 1 := by
  rw [airyPropagator_wave_mixture _ t ht]
  have h := norm_integral_le_of_norm_le_const (μ := airyMixMeasure) (C := 1)
    (f := fun u : ℝ => wavePropagator A
      ((airyTimeScale t : ℂ) * (Real.sqrt u : ℂ))) (Eventually.of_forall (fun u => by
        (try dsimp only)
        rw [← Complex.ofReal_mul]
        exact wavePropagator_posSemidef_norm_le_one A hA _))
  simpa using! h

theorem airyPropagator_norm_le_exp {E : Type*} [NormedRing E] [NormedAlgebra ℂ E]
    [CompleteSpace E] [NormOneClass E] (A : E) (t : ℝ) (ht : 0 ≤ t) :
    ‖airyPropagator A (t : ℂ)‖ ≤ Real.exp (airyTimeScale t * Real.sqrt ‖A‖) := by
  rw [airyPropagator_wave_mixture _ t ht]
  have hmem : ∀ᵐ u : ℝ ∂airyMixMeasure, u ∈ Ioo (0 : ℝ) 1 := betaMeasure_ae_mem
  have h := norm_integral_le_of_norm_le_const (μ := airyMixMeasure)
    (C := Real.exp (airyTimeScale t * Real.sqrt ‖A‖))
    (f := fun u : ℝ => wavePropagator A
      ((airyTimeScale t : ℂ) * (Real.sqrt u : ℂ))) (by
        filter_upwards [hmem] with u hu
        apply (wavePropagator_norm_le_exp A _).trans
        apply Real.exp_le_exp.mpr
        rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg (airyTimeScale_nonneg ht),
          abs_of_nonneg (Real.sqrt_nonneg u)]
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        exact (mul_le_mul_of_nonneg_left (Real.sqrt_le_one.mpr hu.2.le)
          (airyTimeScale_nonneg ht)).trans_eq (mul_one _))
  simpa using! h

end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
