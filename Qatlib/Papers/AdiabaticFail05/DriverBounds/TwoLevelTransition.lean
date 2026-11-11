/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

/-!
# Oscillatory bounds for two-level transitions

This module bounds a transition amplitude given by an oscillatory integral under explicit
differentiability, integrability, and norm hypotheses. The theorem `two_level_amplitude_bound`
gives a bound proportional to `1 / T`, and `two_level_transition_probability_bound` squares it
to bound the transition probability. The mathematical context is
[FarhiGoldstoneGutmannNagaj2008].

## Main statements

* `two_level_amplitude_bound`: Under the stated oscillatory-integral identity,
  differentiability, integrability, and uniform norm bounds, the final transition amplitude
  satisfies `‖c1 θbar‖ ≤ (2 * F + θbar * (F ^ 2 + D)) / T` for positive `T`.
* `two_level_transition_probability_bound`: Under the stated oscillatory-integral and regularity
  hypotheses, the final transition probability satisfies `‖c1 θbar‖ ^ 2 ≤ ((2 * F + θbar * (F ^
  2 + D)) / T) ^ 2` for positive `T`.

## References

* [Farhi et al., 2008][FarhiGoldstoneGutmannNagaj2008]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AdiabaticFail05.DriverBounds

open intervalIntegral MeasureTheory

/-- Under the stated oscillatory-integral identity, differentiability, integrability, and
uniform norm bounds, the final transition amplitude satisfies `‖c1 θbar‖ ≤ (2 * F + θbar *
(F ^ 2 + D)) / T` for positive `T` [FarhiGoldstoneGutmannNagaj2008]. -/
theorem two_level_amplitude_bound
    (c0 c1 f : ℝ → ℂ) (T θbar F D : ℝ)
    (hT : 0 < T) (hθ : 0 ≤ θbar) (hF : 0 ≤ F) (_hD : 0 ≤ D)
    (hc0 : ∀ θ ∈ Set.Icc 0 θbar, ‖c0 θ‖ ≤ 1)
    (_hc1 : ∀ θ ∈ Set.Icc 0 θbar, ‖c1 θ‖ ≤ 1)
    (hf : ∀ θ ∈ Set.Icc 0 θbar, ‖f θ‖ ≤ F)
    (hdf : ∀ θ ∈ Set.Icc 0 θbar, ‖deriv f θ‖ ≤ D)
    (hdc0 : ∀ θ ∈ Set.Icc 0 θbar, ‖deriv c0 θ‖ ≤ F)
    (hc0diff : ∀ θ ∈ Set.uIcc 0 θbar, HasDerivAt c0 (deriv c0 θ) θ)
    (hfdiff : ∀ θ ∈ Set.uIcc 0 θbar, HasDerivAt f (deriv f θ) θ)
    (hint_g' : IntervalIntegrable
      (fun θ => deriv c0 θ * f θ + c0 θ * deriv f θ) volume 0 θbar)
    (hamp : c1 θbar = - ∫ θ in (0 : ℝ)..θbar,
        c0 θ * Complex.exp (Complex.I * ((T : ℂ) * (θ : ℂ))) * f θ) :
    ‖c1 θbar‖ ≤ (2 * F + θbar * (F ^ 2 + D)) / T := by

  set e : ℝ → ℂ := fun θ => Complex.exp (Complex.I * ((T : ℂ) * (θ : ℂ))) with he_def
  set g : ℝ → ℂ := fun θ => c0 θ * f θ with hg_def

  have he_diff : ∀ θ ∈ Set.uIcc 0 θbar, HasDerivAt e (Complex.I * (T : ℂ) * e θ) θ := by
    intro θ _
    have hinner : HasDerivAt (fun x : ℝ => Complex.I * ((T : ℂ) * (x : ℂ)))
        (Complex.I * (T : ℂ)) θ := by
      have h1 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 θ := Complex.ofRealCLM.hasDerivAt
      have h2 : HasDerivAt (fun x : ℝ => (T : ℂ) * (x : ℂ)) ((T : ℂ) * 1) θ :=
        h1.const_mul (T : ℂ)
      have h3 : HasDerivAt (fun x : ℝ => Complex.I * ((T : ℂ) * (x : ℂ)))
          (Complex.I * ((T : ℂ) * 1)) θ := h2.const_mul Complex.I
      simpa using h3
    have hexp : HasDerivAt Complex.exp
        (Complex.exp (Complex.I * ((T : ℂ) * (θ : ℂ)))) (Complex.I * ((T : ℂ) * (θ : ℂ))) :=
      Complex.hasDerivAt_exp _
    have hc := hexp.comp θ hinner
    have hcomp : (Complex.exp ∘ fun x : ℝ => Complex.I * ((T : ℂ) * (x : ℂ))) = e := rfl
    rw [hcomp] at hc
    simpa [e, mul_comm, mul_assoc, mul_left_comm] using hc

  have he_norm : ∀ θ, ‖e θ‖ = 1 := by
    intro θ
    simp only [e]
    rw [Complex.norm_exp]
    have hre : (Complex.I * ((T : ℂ) * (θ : ℂ))).re = 0 := by
      simp [Complex.mul_re]
    rw [hre, Real.exp_zero]
  have he_cont : Continuous e := by
    apply Complex.continuous_exp.comp
    continuity

  have hg_diff : ∀ θ ∈ Set.uIcc 0 θbar,
      HasDerivAt g (deriv c0 θ * f θ + c0 θ * deriv f θ) θ := by
    intro θ hθ
    have h1 := hc0diff θ hθ
    have h2 := hfdiff θ hθ
    have hm := h1.mul h2
    simpa [g, mul_add, add_comm, add_left_comm, mul_comm, mul_assoc, mul_left_comm] using! hm

  have hIv : ‖Complex.I * (T : ℂ)‖ = T := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hT]

  have hg'_bound : ∀ θ ∈ Set.uIcc 0 θbar,
      ‖deriv c0 θ * f θ + c0 θ * deriv f θ‖ ≤ F ^ 2 + D := by
    intro θ hu
    have hmem : θ ∈ Set.Icc 0 θbar := by
      rwa [Set.uIcc_of_le hθ] at hu
    have h1 : ‖deriv c0 θ * f θ‖ ≤ F * F := by
      rw [norm_mul]
      exact mul_le_mul (hdc0 θ hmem) (hf θ hmem) (norm_nonneg _) hF
    have h2 : ‖c0 θ * deriv f θ‖ ≤ 1 * D := by
      rw [norm_mul]
      exact mul_le_mul (hc0 θ hmem) (hdf θ hmem) (norm_nonneg _) (by norm_num)
    calc ‖deriv c0 θ * f θ + c0 θ * deriv f θ‖
        ≤ ‖deriv c0 θ * f θ‖ + ‖c0 θ * deriv f θ‖ := norm_add_le _ _
      _ ≤ F * F + 1 * D := add_le_add h1 h2
      _ = F ^ 2 + D := by ring

  have hint_g'e : IntervalIntegrable
      (fun θ => (deriv c0 θ * f θ + c0 θ * deriv f θ) * e θ) volume 0 θbar :=
    hint_g'.mul_continuousOn he_cont.continuousOn
  have hint_ve : IntervalIntegrable (fun θ => Complex.I * (T : ℂ) * e θ) volume 0 θbar :=
    (he_cont.intervalIntegrable 0 θbar).const_mul (Complex.I * (T : ℂ))

  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (0 : ℝ)) (b := θbar)
    (u := g) (v := e)
    (u' := fun θ => deriv c0 θ * f θ + c0 θ * deriv f θ)
    (v' := fun θ => Complex.I * (T : ℂ) * e θ)
    hg_diff he_diff hint_g' hint_ve

  have hLHS : ∫ θ in (0 : ℝ)..θbar, g θ * (Complex.I * (T : ℂ) * e θ)
      = (Complex.I * (T : ℂ)) * ∫ θ in (0 : ℝ)..θbar, g θ * e θ := by
    have hcongr : (fun θ => g θ * (Complex.I * (T : ℂ) * e θ))
        = (fun θ => (Complex.I * (T : ℂ)) * (g θ * e θ)) := by
      funext θ; ring
    rw [hcongr, intervalIntegral.integral_const_mul]
  rw [hLHS] at hIBP

  have hEq : (Complex.I * (T : ℂ)) * (∫ θ in (0 : ℝ)..θbar, g θ * e θ)
      = g θbar * e θbar - g 0 * e 0
        - ∫ θ in (0 : ℝ)..θbar, (deriv c0 θ * f θ + c0 θ * deriv f θ) * e θ := hIBP

  have hInt_norm : ‖∫ θ in (0 : ℝ)..θbar,
        (deriv c0 θ * f θ + c0 θ * deriv f θ) * e θ‖ ≤ θbar * (F ^ 2 + D) := by
    have hmono : ∫ θ in (0 : ℝ)..θbar,
          ‖(deriv c0 θ * f θ + c0 θ * deriv f θ) * e θ‖
        ≤ ∫ _θ in (0 : ℝ)..θbar, (F ^ 2 + D) := by
      refine intervalIntegral.integral_mono_on hθ hint_g'e.norm
        (intervalIntegrable_const) (fun θ hIcc => ?_)
      have h1 : ‖(deriv c0 θ * f θ + c0 θ * deriv f θ) * e θ‖
          = ‖deriv c0 θ * f θ + c0 θ * deriv f θ‖ := by
        rw [norm_mul, he_norm θ, mul_one]
      rw [h1]
      have huIcc : θ ∈ Set.uIcc 0 θbar := by
        rwa [Set.uIcc_of_le hθ]
      exact hg'_bound θ huIcc
    have hconst : ∫ _θ in (0 : ℝ)..θbar, (F ^ 2 + D) = θbar * (F ^ 2 + D) := by
      simp [intervalIntegral.integral_const, smul_eq_mul]
      ring
    calc ‖∫ θ in (0 : ℝ)..θbar,
            (deriv c0 θ * f θ + c0 θ * deriv f θ) * e θ‖
        ≤ ∫ θ in (0 : ℝ)..θbar,
            ‖(deriv c0 θ * f θ + c0 θ * deriv f θ) * e θ‖ :=
          intervalIntegral.norm_integral_le_integral_norm hθ
      _ ≤ ∫ _θ in (0 : ℝ)..θbar, (F ^ 2 + D) := hmono
      _ = θbar * (F ^ 2 + D) := hconst

  have hBnd : ‖g θbar * e θbar - g 0 * e 0‖ ≤ 2 * F := by
    have hb1 : ‖g θbar * e θbar‖ ≤ F := by
      rw [norm_mul, he_norm θbar, mul_one, hg_def]
      simp only
      calc ‖c0 θbar * f θbar‖ ≤ 1 * F := by
            rw [norm_mul]
            exact mul_le_mul (hc0 θbar ⟨hθ, le_refl θbar⟩) (hf θbar ⟨hθ, le_refl θbar⟩)
              (norm_nonneg _) (by norm_num)
        _ = F := one_mul F
    have hb0 : ‖g 0 * e 0‖ ≤ F := by
      rw [norm_mul, he_norm 0, mul_one, hg_def]
      simp only
      calc ‖c0 0 * f 0‖ ≤ 1 * F := by
            rw [norm_mul]
            exact mul_le_mul (hc0 0 ⟨le_refl 0, hθ⟩) (hf 0 ⟨le_refl 0, hθ⟩)
              (norm_nonneg _) (by norm_num)
        _ = F := one_mul F
    calc ‖g θbar * e θbar - g 0 * e 0‖
        ≤ ‖g θbar * e θbar‖ + ‖g 0 * e 0‖ := norm_sub_le _ _
      _ ≤ F + F := add_le_add hb1 hb0
      _ = 2 * F := by ring

  have hmain : T * ‖∫ θ in (0 : ℝ)..θbar, g θ * e θ‖ ≤ 2 * F + θbar * (F ^ 2 + D) := by
    have hnorm : T * ‖∫ θ in (0 : ℝ)..θbar, g θ * e θ‖
        = ‖(Complex.I * (T : ℂ)) * (∫ θ in (0 : ℝ)..θbar, g θ * e θ)‖ := by
      rw [norm_mul, hIv]
    rw [hnorm, hEq]
    calc ‖g θbar * e θbar - g 0 * e 0
            - ∫ θ in (0 : ℝ)..θbar, (deriv c0 θ * f θ + c0 θ * deriv f θ) * e θ‖
        ≤ ‖g θbar * e θbar - g 0 * e 0‖
            + ‖∫ θ in (0 : ℝ)..θbar, (deriv c0 θ * f θ + c0 θ * deriv f θ) * e θ‖ :=
          norm_sub_le _ _
      _ ≤ 2 * F + θbar * (F ^ 2 + D) := add_le_add hBnd hInt_norm

  have hamp' : ‖c1 θbar‖ = ‖∫ θ in (0 : ℝ)..θbar, g θ * e θ‖ := by
    rw [hamp, norm_neg]
    congr 1
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [g, e]
    ring
  rw [hamp'] at *

  rw [le_div_iff₀ hT]
  linarith [hmain]

/-- Under the stated oscillatory-integral and regularity hypotheses, the final transition
probability satisfies `‖c1 θbar‖ ^ 2 ≤ ((2 * F + θbar * (F ^ 2 + D)) / T) ^ 2` for positive
`T` [FarhiGoldstoneGutmannNagaj2008]. -/
theorem two_level_transition_probability_bound
    (c0 c1 f : ℝ → ℂ) (T θbar F D : ℝ)
    (hT : 0 < T) (hθ : 0 ≤ θbar) (hF : 0 ≤ F) (hD : 0 ≤ D)
    (hc0 : ∀ θ ∈ Set.Icc 0 θbar, ‖c0 θ‖ ≤ 1)
    (hc1 : ∀ θ ∈ Set.Icc 0 θbar, ‖c1 θ‖ ≤ 1)
    (hf : ∀ θ ∈ Set.Icc 0 θbar, ‖f θ‖ ≤ F)
    (hdf : ∀ θ ∈ Set.Icc 0 θbar, ‖deriv f θ‖ ≤ D)
    (hdc0 : ∀ θ ∈ Set.Icc 0 θbar, ‖deriv c0 θ‖ ≤ F)
    (hc0diff : ∀ θ ∈ Set.uIcc 0 θbar, HasDerivAt c0 (deriv c0 θ) θ)
    (hfdiff : ∀ θ ∈ Set.uIcc 0 θbar, HasDerivAt f (deriv f θ) θ)
    (hint_g' : IntervalIntegrable
      (fun θ => deriv c0 θ * f θ + c0 θ * deriv f θ) volume 0 θbar)
    (hamp : c1 θbar = - ∫ θ in (0 : ℝ)..θbar,
        c0 θ * Complex.exp (Complex.I * ((T : ℂ) * (θ : ℂ))) * f θ) :
    ‖c1 θbar‖ ^ 2 ≤ ((2 * F + θbar * (F ^ 2 + D)) / T) ^ 2 := by
  have h := two_level_amplitude_bound c0 c1 f T θbar F D hT hθ hF hD hc0 hc1 hf hdf
    hdc0 hc0diff hfdiff hint_g' hamp
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

end Qatlib.Papers.AdiabaticFail05.DriverBounds
