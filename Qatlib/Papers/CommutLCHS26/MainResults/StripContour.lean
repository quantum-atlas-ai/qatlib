/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Fourier.FourierTransform

/-!
# Contour shifts and Fourier decay on strips

This module proves contour-shift identities for vector-valued holomorphic functions with uniform
decay on horizontal strips. Multiplying by `phase` turns these identities into the exponential
Fourier bounds used in the quadrature analysis of [AftabAnTrivisa2026].

## Main statements

* `integral_shift`: invariance of integrals under a horizontal contour shift.
* `norm_fourier_le`: exponential decay of the real-axis Fourier transform.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.StripContour

open Complex Set Filter MeasureTheory
open scoped Topology
open scoped FourierTransform

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Uniform decay of `f (x + y I)` as `|x|` tends to infinity, uniformly for `y` in the closed
interval `[a, b]`. -/
def UniformDecay (f : ℂ → E) (a b : ℝ) : Prop :=
  ∀ ε > 0, ∃ R : ℝ, ∀ x : ℝ, R ≤ |x| →
    ∀ y ∈ Icc a b, ‖f ((x : ℂ) + y * I)‖ ≤ ε

omit [NormedSpace ℂ E] in

/-- Uniform decay on a horizontal strip restricts to any smaller strip. -/
theorem UniformDecay.mono {f : ℂ → E} {a b c d : ℝ} (hf : UniformDecay f a b)
    (hac : a ≤ c) (hdb : d ≤ b) : UniformDecay f c d := by
  intro ε hε
  obtain ⟨R, hR⟩ := hf ε hε
  exact ⟨R, fun x hx y hy => hR x hx y ⟨hac.trans hy.1, hy.2.trans hdb⟩⟩

/-- The difference between the horizontal integrals on a rectangle is bounded by twice the side
bound times the strip height. -/
theorem rectangle_shift_bound (f : ℂ → E) (a b R C : ℝ) (hab : a ≤ b)
    (hf : DifferentiableOn ℂ f {z : ℂ | a ≤ z.im ∧ z.im ≤ b})
    (hleft : ∀ y ∈ Icc a b, ‖f ((-R : ℝ) + y * I)‖ ≤ C)
    (hright : ∀ y ∈ Icc a b, ‖f ((R : ℂ) + y * I)‖ ≤ C) :
    ‖(∫ x : ℝ in -R..R, f ((x : ℂ) + a * I)) -
      (∫ x : ℝ in -R..R, f ((x : ℂ) + b * I))‖ ≤ 2 * (C * (b - a)) := by
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    ((-R : ℝ) + a * I) ((R : ℂ) + b * I) (hf.mono (by
      intro z hz
      simpa [uIcc_of_le hab] using hz.2))
  simp only [add_re, add_im, ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im,
    mul_zero, mul_one, sub_zero, zero_add, add_zero] at hrect
  have hid : (∫ x : ℝ in -R..R, f ((x : ℂ) + a * I)) -
      (∫ x : ℝ in -R..R, f ((x : ℂ) + b * I)) =
      I • (∫ y : ℝ in a..b, f ((-R : ℝ) + y * I)) -
      I • (∫ y : ℝ in a..b, f ((R : ℂ) + y * I)) := by
    exact eq_sub_iff_add_eq.mpr (sub_eq_zero.mp hrect)
  rw [hid]
  have hl : ‖∫ y : ℝ in a..b, f ((-R : ℝ) + y * I)‖ ≤ C * |b - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun y hy =>
      hleft y (Ioc_subset_Icc_self (by simpa only [uIoc_of_le hab] using hy)))
  have hr : ‖∫ y : ℝ in a..b, f ((R : ℂ) + y * I)‖ ≤ C * |b - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun y hy =>
      hright y (Ioc_subset_Icc_self (by simpa only [uIoc_of_le hab] using hy)))
  calc
    _ ≤ ‖I • (∫ y : ℝ in a..b, f ((-R : ℝ) + y * I))‖ +
        ‖I • (∫ y : ℝ in a..b, f ((R : ℂ) + y * I))‖ := norm_sub_le _ _
    _ ≤ C * |b - a| + C * |b - a| := by
      simpa only [norm_smul, norm_I, one_mul] using add_le_add hl hr
    _ = 2 * (C * (b - a)) := by rw [abs_of_nonneg (sub_nonneg.mpr hab)]; ring

/-- For a holomorphic function with uniform horizontal decay, integrable horizontal slices at
the strip boundaries have equal integrals. -/
theorem integral_shift [CompleteSpace E] (f : ℂ → E) (a b : ℝ) (hab : a ≤ b)
    (hf : DifferentiableOn ℂ f {z : ℂ | a ≤ z.im ∧ z.im ≤ b})
    (hdecay : UniformDecay f a b)
    (ha : Integrable (fun x : ℝ => f ((x : ℂ) + a * I)))
    (hb : Integrable (fun x : ℝ => f ((x : ℂ) + b * I))) :
    (∫ x : ℝ, f ((x : ℂ) + a * I)) = ∫ x : ℝ, f ((x : ℂ) + b * I) := by
  have hlim := (intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id).sub
    (intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id)
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨R₀, hR₀⟩ := hdecay (ε / (2 * (b - a + 1))) (by positivity)
  have hbound : ∀ᶠ R : ℝ in atTop,
      ‖(∫ x : ℝ in -R..R, f ((x : ℂ) + a * I)) -
        (∫ x : ℝ in -R..R, f ((x : ℂ) + b * I))‖ ≤ ε := by
    filter_upwards [eventually_ge_atTop (max R₀ 0)] with R hR
    have hRpos : 0 ≤ R := (le_max_right _ _).trans hR
    have hRR : R₀ ≤ R := (le_max_left _ _).trans hR
    refine (rectangle_shift_bound f a b R _ hab hf
      (fun y hy => hR₀ (-R) (by simpa [abs_neg, abs_of_nonneg hRpos] using hRR) y hy)
      (fun y hy => hR₀ R (by simpa [abs_of_nonneg hRpos] using hRR) y hy)).trans ?_
    calc
      _ = ε * (b - a) / (b - a + 1) := by
        field_simp
      _ ≤ ε := (div_le_iff₀ (by linarith : 0 < b - a + 1)).mpr (by nlinarith)
  simpa only [zero_add] using le_of_tendsto hlim.norm hbound

/-- The complex exponential phase `exp (-(ω I) z)`. -/
def phase (ω : ℝ) (z : ℂ) : ℂ := Complex.exp (-((ω : ℂ) * I) * z)

/-- The phase norm on the horizontal line at height `y` equals `exp (ω y)`. -/
theorem phase_norm (ω x y : ℝ) :
    ‖phase ω ((x : ℂ) + y * I)‖ = Real.exp (ω * y) := by
  simp [phase, Complex.norm_exp, mul_re, mul_im]

/-- Multiplying an integrable horizontal slice by the complex exponential phase preserves
integrability. -/
theorem integrable_phase (f : ℂ → E) (ω y : ℝ)
    (hf : Integrable (fun x : ℝ => f ((x : ℂ) + y * I))) :
    Integrable (fun x : ℝ => phase ω ((x : ℂ) + y * I) • f ((x : ℂ) + y * I)) := by
  apply hf.bdd_smul (Real.exp (ω * y))
  · apply Continuous.aestronglyMeasurable
    unfold phase
    fun_prop
  · exact Eventually.of_forall (fun x => (phase_norm ω x y).le)

/-- Multiplication by the complex exponential phase preserves uniform decay on a fixed
horizontal strip. -/
theorem UniformDecay.mul_phase {f : ℂ → E} {a b : ℝ} (hf : UniformDecay f a b) (ω : ℝ) :
    UniformDecay (fun z => phase ω z • f z) a b := by
  let C := Real.exp (|ω| * max |a| |b|)
  have hC : 0 < C := Real.exp_pos _
  intro ε hε
  obtain ⟨R, hR⟩ := hf (ε / C) (div_pos hε hC)
  refine ⟨R, fun x hx y hy => ?_⟩
  have hyabs : |y| ≤ max |a| |b| := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le a, le_max_left |a| |b|, hy.1]
    · exact hy.2.trans ((le_abs_self b).trans (le_max_right _ _))
  have hphase : ‖phase ω ((x : ℂ) + y * I)‖ ≤ C := by
    rw [phase_norm]
    apply Real.exp_le_exp.mpr
    exact (le_abs_self (ω * y)).trans (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hyabs (abs_nonneg _))
  rw [norm_smul]
  calc
    _ ≤ C * (ε / C) := mul_le_mul hphase (hR x hx y hy) (norm_nonneg _) (le_of_lt hC)
    _ = ε := by field_simp

/-- The phase-weighted horizontal integrals of a holomorphic, uniformly decaying function agree
at the strip boundaries when the slices are integrable. -/
theorem phase_integral_shift [CompleteSpace E] (f : ℂ → E) (a b ω : ℝ) (hab : a ≤ b)
    (hf : DifferentiableOn ℂ f {z : ℂ | a ≤ z.im ∧ z.im ≤ b})
    (hdecay : UniformDecay f a b)
    (ha : Integrable (fun x : ℝ => f ((x : ℂ) + a * I)))
    (hb : Integrable (fun x : ℝ => f ((x : ℂ) + b * I))) :
    (∫ x : ℝ, phase ω ((x : ℂ) + a * I) • f ((x : ℂ) + a * I)) =
      ∫ x : ℝ, phase ω ((x : ℂ) + b * I) • f ((x : ℂ) + b * I) := by
  apply integral_shift _ a b hab _ (hdecay.mul_phase ω)
    (integrable_phase f ω a ha) (integrable_phase f ω b hb)
  apply DifferentiableOn.smul _ hf
  exact (Complex.differentiable_exp.comp
    ((differentiable_const _).mul differentiable_id)).differentiableOn

/-- A bound `M` on the horizontal norm integral gives the phase-weighted integral bound `exp (ω
y) M`. -/
theorem phase_integral_norm (f : ℂ → E) (ω y M : ℝ)
    (hmass : (∫ x : ℝ, ‖f ((x : ℂ) + y * I)‖) ≤ M) :
    ‖∫ x : ℝ, phase ω ((x : ℂ) + y * I) • f ((x : ℂ) + y * I)‖ ≤
      Real.exp (ω * y) * M := by
  calc
    _ ≤ ∫ x : ℝ, ‖phase ω ((x : ℂ) + y * I) • f ((x : ℂ) + y * I)‖ :=
      norm_integral_le_integral_norm _
    _ = Real.exp (ω * y) * ∫ x : ℝ, ‖f ((x : ℂ) + y * I)‖ := by
      simp only [norm_smul, phase_norm, integral_const_mul]
    _ ≤ Real.exp (ω * y) * M := mul_le_mul_of_nonneg_left hmass (Real.exp_nonneg _)

/-- Strip analyticity, uniform decay, and bounded integrable horizontal slices give exponential
Fourier-integral decay `exp (-|ω| ρ) M`. -/
theorem fourier_decay [CompleteSpace E] (f : ℂ → E) (ρ M ω : ℝ) (hρ : 0 ≤ ρ)
    (hf : DifferentiableOn ℂ f {z : ℂ | -ρ ≤ z.im ∧ z.im ≤ ρ})
    (hdecay : UniformDecay f (-ρ) ρ)
    (hint : ∀ y ∈ Icc (-ρ) ρ, Integrable (fun x : ℝ => f ((x : ℂ) + y * I)))
    (hmass : ∀ y ∈ Icc (-ρ) ρ, (∫ x : ℝ, ‖f ((x : ℂ) + y * I)‖) ≤ M) :
    ‖∫ x : ℝ, phase ω (x : ℂ) • f (x : ℂ)‖ ≤ Real.exp (-|ω| * ρ) * M := by
  have hzero : (0 : ℝ) ∈ Icc (-ρ) ρ := ⟨by linarith, hρ⟩
  by_cases hω : 0 ≤ ω
  · have hneg : -ρ ∈ Icc (-ρ) ρ := ⟨le_rfl, by linarith⟩
    have hs := phase_integral_shift f (-ρ) 0 ω (by linarith)
      (hf.mono (by intro z hz; exact ⟨hz.1, hz.2.trans hρ⟩))
      (hdecay.mono le_rfl hρ) (hint _ hneg) (hint _ hzero)
    have hn := phase_integral_norm f ω (-ρ) M (hmass _ hneg)
    rw [hs] at hn
    simpa only [ofReal_zero, zero_mul, add_zero, abs_of_nonneg hω, mul_neg, neg_mul] using hn
  · have hpos : ρ ∈ Icc (-ρ) ρ := ⟨by linarith, le_rfl⟩
    have hs := phase_integral_shift f 0 ρ ω hρ
      (hf.mono (by intro z hz; exact ⟨(by linarith : -ρ ≤ 0).trans hz.1, hz.2⟩))
      (hdecay.mono (by linarith) le_rfl) (hint _ hzero) (hint _ hpos)
    have hn := phase_integral_norm f ω ρ M (hmass _ hpos)
    rw [← hs] at hn
    simpa only [ofReal_zero, zero_mul, add_zero, abs_of_neg (lt_of_not_ge hω), neg_neg] using hn

/-- The same exponential Fourier-integral bound follows when integrability and mass bounds are
required only on interior horizontal slices. -/
theorem fourier_decay_of_interior_mass [CompleteSpace E] (f : ℂ → E) (ρ M ω : ℝ)
    (hρ : 0 < ρ)
    (hf : DifferentiableOn ℂ f {z : ℂ | -ρ ≤ z.im ∧ z.im ≤ ρ})
    (hdecay : UniformDecay f (-ρ) ρ)
    (hint : ∀ y ∈ Ioo (-ρ) ρ, Integrable (fun x : ℝ => f ((x : ℂ) + y * I)))
    (hmass : ∀ y ∈ Ioo (-ρ) ρ, (∫ x : ℝ, ‖f ((x : ℂ) + y * I)‖) ≤ M) :
    ‖∫ x : ℝ, phase ω (x : ℂ) • f (x : ℂ)‖ ≤ Real.exp (-|ω| * ρ) * M := by
  have hc : Continuous (fun r : ℝ => Real.exp (-|ω| * r) * M) := by fun_prop
  apply le_of_tendsto_of_tendsto tendsto_const_nhds
    (hc.continuousWithinAt.tendsto : Tendsto _ (𝓝[<] ρ) _)
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Ioi_mem_nhds hρ)] with r hr hrpos
  change r < ρ at hr
  change 0 < r at hrpos
  have hsubset : Icc (-r) r ⊆ Ioo (-ρ) ρ := by
    intro y hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  exact fourier_decay f r M ω hrpos.le
    (hf.mono (by intro z hz; exact ⟨by linarith [hz.1], by linarith [hz.2]⟩))
    (hdecay.mono (by linarith) hr.le)
    (fun y hy => hint y (hsubset hy)) (fun y hy => hmass y (hsubset hy))

/-- The Fourier transform of the real-axis restriction is bounded by `exp (-2πρ |ξ|) M` under
the stated strip hypotheses; see [Aftab et al., Lemma 4.13][AftabAnTrivisa2026]. -/
theorem norm_fourier_le [CompleteSpace E] (f : ℂ → E) (ρ M ξ : ℝ) (hρ : 0 < ρ)
    (hf : DifferentiableOn ℂ f {z : ℂ | -ρ ≤ z.im ∧ z.im ≤ ρ})
    (hdecay : UniformDecay f (-ρ) ρ)
    (hint : ∀ y ∈ Ioo (-ρ) ρ, Integrable (fun x : ℝ => f ((x : ℂ) + y * I)))
    (hmass : ∀ y ∈ Ioo (-ρ) ρ, (∫ x : ℝ, ‖f ((x : ℂ) + y * I)‖) ≤ M) :
    ‖𝓕 (fun x : ℝ => f (x : ℂ)) ξ‖ ≤ Real.exp (-(2 * Real.pi * ρ * |ξ|)) * M := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hp : (fun x : ℝ => Complex.exp (↑(-2 * Real.pi * x * ξ) * I) • f (x : ℂ)) =
      (fun x : ℝ => phase (2 * Real.pi * ξ) (x : ℂ) • f (x : ℂ)) := by
    funext x
    congr 1
    unfold phase
    congr 1
    push_cast
    ring
  rw [hp]
  have hw : |2 * Real.pi * ξ| = 2 * Real.pi * |ξ| := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  calc
    _ ≤ Real.exp (-|2 * Real.pi * ξ| * ρ) * M :=
      fourier_decay_of_interior_mass f ρ M _ hρ hf hdecay hint hmass
    _ = _ := by rw [hw]; congr 2; ring

end Qatlib.Papers.CommutLCHS26.MainResults.StripContour
