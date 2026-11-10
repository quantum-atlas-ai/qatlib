/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 800000
open Qatlib.Foundations.PureStateMath
namespace Qatlib.Concepts.HhlErrorBridge.FilterStability
open Matrix
open scoped Real

private theorem norm_toLp_sq (v : QState (Fin 3)) :
    ‖WithLp.toLp 2 v‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]

noncomputable def sinEnvelopeFilterF (d θ : ℝ) : ℝ :=
  if 2 * d ≤ θ then d / θ
  else if d ≤ θ then (1 / 2) * Real.sin (Real.pi / 2 * (θ - d) / d) else 0

noncomputable def sinEnvelopeFilterG (d θ : ℝ) : ℝ :=
  if 2 * d ≤ θ then 0
  else if d ≤ θ then (1 / 2) * Real.cos (Real.pi / 2 * (θ - d) / d) else 1 / 2

noncomputable def sinEnvelopeHVector (d θ : ℝ) : QState (Fin 3) :=
  fun s =>
    if s = 0 then
      (Real.sqrt (1 - sinEnvelopeFilterF d θ ^ 2 - sinEnvelopeFilterG d θ ^ 2) : ℂ)
    else if s = 1 then (sinEnvelopeFilterF d θ : ℂ) else (sinEnvelopeFilterG d θ : ℂ)

noncomputable def sinEnvelopeFlagMass (d θ : ℝ) : ℝ :=
  sinEnvelopeFilterF d θ ^ 2 + sinEnvelopeFilterG d θ ^ 2

theorem sin_envelope_filter_bounded (d θ : ℝ) (hd : 0 < d) :
    sinEnvelopeFlagMass d θ ≤ 1 / 4 := by
  unfold sinEnvelopeFlagMass sinEnvelopeFilterF sinEnvelopeFilterG
  split_ifs with hwell hramp
  · have hθ : 0 < θ := by linarith
    have hlo : 0 ≤ d / θ := div_nonneg hd.le hθ.le
    have hhi : d / θ ≤ 1 / 2 := (div_le_iff₀ hθ).2 (by linarith)
    nlinarith
  · nlinarith [Real.sin_sq_add_cos_sq (Real.pi / 2 * (θ - d) / d)]
  · norm_num

theorem sin_envelope_filter_branch_values (d : ℝ) (hd : 0 < d) :
    sinEnvelopeFilterF d (2 * d) = 1 / 2 ∧ sinEnvelopeFilterG d (2 * d) = 0 ∧
      sinEnvelopeFilterF d d = 0 ∧ sinEnvelopeFilterG d d = 1 / 2 ∧
      sinEnvelopeFilterF d 0 = 0 ∧ sinEnvelopeFilterG d 0 = 1 / 2 ∧
      sinEnvelopeFilterF d (-1 / 4) = 0 ∧ sinEnvelopeFilterG d (-1 / 4) = 1 / 2 ∧
      (∀ θ, 2 * d ≤ θ → sinEnvelopeFilterF d θ = d / θ ∧
        sinEnvelopeFilterG d θ = 0) := by
  have hdd : ¬ 2 * d ≤ d := by linarith
  have hd0 : ¬ d ≤ 0 := by linarith
  have h2d0 : ¬ 2 * d ≤ 0 := by linarith
  have hdn : ¬ d ≤ -1 / 4 := by linarith
  have h2dn : ¬ 2 * d ≤ -1 / 4 := by linarith
  have hdiv : d / (2 * d) = 1 / 2 := by field_simp
  simp [sinEnvelopeFilterF, sinEnvelopeFilterG, hdd, hd0, h2d0, hdn, h2dn, hdiv]
  intro θ hθ
  simp [not_lt_of_ge hθ]

theorem sin_envelope_h_normalized (d θ : ℝ) (hd : 0 < d) :
    ∑ s : Fin 3, ‖sinEnvelopeHVector d θ s‖ ^ 2 = 1 := by
  have hbound := sin_envelope_filter_bounded d θ hd
  have hrad : 0 ≤ 1 - sinEnvelopeFilterF d θ ^ 2 - sinEnvelopeFilterG d θ ^ 2 := by
    unfold sinEnvelopeFlagMass at hbound
    linarith
  simp [Fin.sum_univ_succ, sinEnvelopeHVector, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, Real.sq_sqrt hrad]

theorem sin_envelope_filter_nonnegative (d θ : ℝ) (hd : 0 < d) :
    0 ≤ sinEnvelopeFilterF d θ ∧ 0 ≤ sinEnvelopeFilterG d θ := by
  unfold sinEnvelopeFilterF sinEnvelopeFilterG
  split_ifs with hw hr
  · have hθ : 0 < θ := by linarith
    exact ⟨div_nonneg hd.le hθ.le, le_rfl⟩
  · have ha : 0 ≤ Real.pi / 2 * (θ-d) / d := by positivity
    have hb : Real.pi / 2 * (θ-d) / d ≤ Real.pi / 2 := by
      apply (div_le_iff₀ hd).mpr
      nlinarith [Real.pi_pos]
    exact ⟨mul_nonneg (by norm_num)
        (Real.sin_nonneg_of_nonneg_of_le_pi ha (by linarith [Real.pi_pos])),
      mul_nonneg (by norm_num) (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hb⟩)⟩
  · norm_num

private theorem sin_envelope_ramp_values (d θ : ℝ) (hd : 0 < d)
    (hl : d ≤ θ) (hu : θ ≤ 2*d) :
    sinEnvelopeFilterF d θ = (1/2) * Real.sin (Real.pi/2*(θ-d)/d) ∧
      sinEnvelopeFilterG d θ = (1/2) * Real.cos (Real.pi/2*(θ-d)/d) := by
  by_cases he : θ = 2*d
  · subst θ
    have ha : Real.pi/2*(2*d-d)/d = Real.pi/2 := by field_simp; ring
    rw [ha, Real.sin_pi_div_two, Real.cos_pi_div_two]
    exact ⟨by simpa using (sin_envelope_filter_branch_values d hd).1,
      by simpa using (sin_envelope_filter_branch_values d hd).2.1⟩
  · have hw : ¬ 2*d ≤ θ := by
      intro hh
      exact he (le_antisymm hu hh)
    simp [sinEnvelopeFilterF, sinEnvelopeFilterG, hw, hl]

private theorem sin_envelope_ramp_nothing (d θ : ℝ) (hd : 0 < d)
    (hl : d ≤ θ) (hu : θ ≤ 2*d) :
    sinEnvelopeHVector d θ 0 = (Real.sqrt (3/4) : ℂ) := by
  have hv := sin_envelope_ramp_values d θ hd hl hu
  have hm : 1-sinEnvelopeFilterF d θ ^ 2-sinEnvelopeFilterG d θ ^ 2 = (3/4 : ℝ) := by
    rw [hv.1, hv.2]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi/2*(θ-d)/d)]
  simp [sinEnvelopeHVector, hm]

theorem sin_envelope_h_ramp_lipschitz (d θ₁ θ₂ : ℝ) (hd : 0 < d)
    (h₁ : d ≤ θ₁) (h₁' : θ₁ ≤ 2*d) (h₂ : d ≤ θ₂) (h₂' : θ₂ ≤ 2*d) :
    ‖WithLp.toLp 2 (sinEnvelopeHVector d θ₁ - sinEnvelopeHVector d θ₂)‖ ≤
      (Real.pi/(4*d))*|θ₁-θ₂| := by
  let a := Real.pi/2*(θ₁-d)/d
  let b := Real.pi/2*(θ₂-d)/d
  have hv₁ := sin_envelope_ramp_values d θ₁ hd h₁ h₁'
  have hv₂ := sin_envelope_ramp_values d θ₂ hd h₂ h₂'
  have hc : (Real.sin a-Real.sin b)^2 + (Real.cos a-Real.cos b)^2 =
      2*(1-Real.cos (a-b)) := by
    rw [Real.cos_sub]
    nlinarith [Real.sin_sq_add_cos_sq a, Real.sin_sq_add_cos_sq b]
  have hm : ‖WithLp.toLp 2 (sinEnvelopeHVector d θ₁ - sinEnvelopeHVector d θ₂)‖^2 =
      (1/2)*(1-Real.cos (a-b)) := by
    rw [norm_toLp_sq]
    have hs : (∑ s : Fin 3, ‖(sinEnvelopeHVector d θ₁ - sinEnvelopeHVector d θ₂) s‖^2) =
        ‖sinEnvelopeHVector d θ₁ 0 - sinEnvelopeHVector d θ₂ 0‖^2 +
        ‖sinEnvelopeHVector d θ₁ 1 - sinEnvelopeHVector d θ₂ 1‖^2 +
        ‖sinEnvelopeHVector d θ₁ 2 - sinEnvelopeHVector d θ₂ 2‖^2 := by
      simp [Fin.sum_univ_succ, add_assoc]
    rw [hs, sin_envelope_ramp_nothing d θ₁ hd h₁ h₁',
      sin_envelope_ramp_nothing d θ₂ hd h₂ h₂']
    simp [sinEnvelopeHVector, hv₁.1, hv₁.2, hv₂.1, hv₂.2,
      -Complex.ofReal_sin, -Complex.ofReal_cos]
    simp only [show (2 : ℂ)⁻¹ = ((1/2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    dsimp [a, b] at hc ⊢
    nlinarith [hc]
  have hab : a-b = (Real.pi/(2*d))*(θ₁-θ₂) := by dsimp [a,b]; ring
  have hcos := Real.one_sub_sq_div_two_le_cos (x := a-b)
  have he : (a-b)^2 / 4 = ((Real.pi/(4*d))*|θ₁-θ₂|)^2 := by
    simp only [hab, mul_pow, sq_abs]
    field_simp
    ring
  have hn := norm_nonneg (WithLp.toLp 2 (sinEnvelopeHVector d θ₁ - sinEnvelopeHVector d θ₂))
  have hr : 0 ≤ (Real.pi/(4*d))*|θ₁-θ₂| := by positivity
  nlinarith

theorem sin_envelope_h_well_lipschitz (d x y : ℝ) (hd : 0 < d)
    (hx : 2*d ≤ x) (hxy : x ≤ y) :
    ‖WithLp.toLp 2 (sinEnvelopeHVector d x - sinEnvelopeHVector d y)‖ ≤
      (1/d)*(y-x) := by
  have hy : 2*d ≤ y := hx.trans hxy
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  let f := d/x
  let g := d/y
  let a := Real.sqrt (1-f^2)
  let b := Real.sqrt (1-g^2)
  have hf0 : 0 ≤ f := div_nonneg hd.le hx0.le
  have hg0 : 0 ≤ g := div_nonneg hd.le hy0.le
  have hfg : g ≤ f := div_le_div_of_nonneg_left hd.le hx0 hxy
  have hf : f ≤ 1/2 := (div_le_iff₀ hx0).mpr (by linarith)
  have hg : g ≤ 1/2 := hfg.trans hf
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have ha : a^2 = 1-f^2 := Real.sq_sqrt (by nlinarith)
  have hb : b^2 = 1-g^2 := Real.sq_sqrt (by nlinarith)
  have hab : a ≤ b := Real.sqrt_le_sqrt (by nlinarith)
  have hab1 : 1 ≤ a+b := by nlinarith
  have hsumfg : f+g ≤ 1 := by linarith
  have hm₁ := mul_le_mul_of_nonneg_left hab1 (sub_nonneg.mpr hab)
  have hm₂ := mul_le_mul_of_nonneg_left hsumfg (sub_nonneg.mpr hfg)
  have hdiff : b-a ≤ f-g := by nlinarith
  have hsq : ‖WithLp.toLp 2 (sinEnvelopeHVector d x - sinEnvelopeHVector d y)‖^2 =
      (a-b)^2+(f-g)^2 := by
    rw [norm_toLp_sq]
    simp [Fin.sum_univ_succ, sinEnvelopeHVector, sinEnvelopeFilterF, sinEnvelopeFilterG,
      hx, hy, a, b, f, g, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, sq_abs, -Complex.ofReal_div]
  have hnorm : ‖WithLp.toLp 2 (sinEnvelopeHVector d x - sinEnvelopeHVector d y)‖ ≤
      2*(f-g) := by
    have := norm_nonneg (WithLp.toLp 2 (sinEnvelopeHVector d x - sinEnvelopeHVector d y))
    nlinarith
  have hdif : f-g = d*(y-x)/(x*y) := by
    dsimp [f,g]
    field_simp
  have hden : 4*d^2 ≤ x*y := by nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]
  have hrat : f-g ≤ (y-x)/(4*d) := by
    rw [hdif]
    calc
      _ ≤ d*(y-x)/(4*d^2) := div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = _ := by field_simp
  have he : (1/d)*(y-x) = 4*((y-x)/(4*d)) := by ring
  rw [he]
  have hnn : 0 ≤ (y-x)/(4*d) := by positivity
  linarith

private theorem sin_envelope_h_low (d x : ℝ) (hd : 0 < d) (hx : x ≤ d) :
    sinEnvelopeHVector d x = sinEnvelopeHVector d d := by
  by_cases he : x = d
  · rw [he]
  · have hxd : ¬ d ≤ x := by intro h; exact he (le_antisymm hx h)
    have hxd2 : ¬ 2*d ≤ x := by linarith
    have hdd2 : ¬ 2*d ≤ d := by linarith
    ext s
    simp [sinEnvelopeHVector, sinEnvelopeFilterF, sinEnvelopeFilterG, hxd, hxd2, hdd2]

private theorem sin_envelope_h_triangle (d x z y : ℝ) :
    ‖WithLp.toLp 2 (sinEnvelopeHVector d x - sinEnvelopeHVector d y)‖ ≤
      ‖WithLp.toLp 2 (sinEnvelopeHVector d x - sinEnvelopeHVector d z)‖ +
        ‖WithLp.toLp 2 (sinEnvelopeHVector d z - sinEnvelopeHVector d y)‖ := by
  calc
    _ = ‖WithLp.toLp 2 (sinEnvelopeHVector d x - sinEnvelopeHVector d z) +
        WithLp.toLp 2 (sinEnvelopeHVector d z - sinEnvelopeHVector d y)‖ := by
      congr 1
      ext s
      simp [WithLp.toLp]
    _ ≤ _ := norm_add_le _ _

private theorem sin_envelope_h_ramp_coarse (d x y : ℝ) (hd : 0 < d)
    (hx : d ≤ x) (hxy : x ≤ y) (hy : y ≤ 2*d) :
    ‖WithLp.toLp 2 (sinEnvelopeHVector d x - sinEnvelopeHVector d y)‖ ≤
      (1/d)*(y-x) := by
  have hp := sin_envelope_h_ramp_lipschitz d x y hd hx (hxy.trans hy) (hx.trans hxy) hy
  have hcoef : Real.pi/(4*d) ≤ 1/d := by
    calc
      _ = (Real.pi/4)/d := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith [Real.pi_lt_four]) hd.le
  have hp' := hp.trans (mul_le_mul_of_nonneg_right hcoef (abs_nonneg (x-y)))
  rwa [abs_of_nonpos (by linarith), neg_sub] at hp'

private theorem sin_envelope_h_ordered_lipschitz (d x y : ℝ) (hd : 0 < d) (hxy : x ≤ y) :
    ‖WithLp.toLp 2 (sinEnvelopeHVector d x - sinEnvelopeHVector d y)‖ ≤
      (1/d)*(y-x) := by
  have hdinv : 0 < 1/d := by positivity
  by_cases hx : d ≤ x
  · by_cases hw : 2*d ≤ x
    · exact sin_envelope_h_well_lipschitz d x y hd hw hxy
    · by_cases hy : y ≤ 2*d
      · exact sin_envelope_h_ramp_coarse d x y hd hx hxy hy
      · have hb := sin_envelope_h_ramp_coarse d x (2*d) hd hx (by linarith) le_rfl
        have hw' := sin_envelope_h_well_lipschitz d (2*d) y hd le_rfl (by linarith)
        have ht := sin_envelope_h_triangle d x (2*d) y
        linarith
  · rw [sin_envelope_h_low d x hd (by linarith)]
    by_cases hy : y ≤ d
    · rw [sin_envelope_h_low d y hd hy, sub_self]
      simp [WithLp.toLp]
      positivity
    · by_cases hw : y ≤ 2*d
      · have hb := sin_envelope_h_ramp_coarse d d y hd le_rfl (by linarith) hw
        nlinarith
      · have hb := sin_envelope_h_ramp_coarse d d (2*d) hd le_rfl (by linarith) le_rfl
        have hw' := sin_envelope_h_well_lipschitz d (2*d) y hd le_rfl (by linarith)
        have ht := sin_envelope_h_triangle d d (2*d) y
        nlinarith

theorem sin_envelope_h_lipschitz (d θ₁ θ₂ : ℝ) (hd : 0 < d) :
    Real.sqrt (∑ s : Fin 3, ‖(sinEnvelopeHVector d θ₁ - sinEnvelopeHVector d θ₂) s‖^2) ≤
      (1/d)*|θ₁-θ₂| := by
  rw [← norm_toLp_sq, Real.sqrt_sq (norm_nonneg _)]
  rcases le_total θ₁ θ₂ with h | h
  · have hp := sin_envelope_h_ordered_lipschitz d θ₁ θ₂ hd h
    rwa [abs_of_nonpos (by linarith), neg_sub]
  · have hp := sin_envelope_h_ordered_lipschitz d θ₂ θ₁ hd h
    have hn : ‖WithLp.toLp 2 (sinEnvelopeHVector d θ₁ - sinEnvelopeHVector d θ₂)‖ =
        ‖WithLp.toLp 2 (sinEnvelopeHVector d θ₂ - sinEnvelopeHVector d θ₁)‖ := by
      change ‖WithLp.toLp 2 (sinEnvelopeHVector d θ₁) -
        WithLp.toLp 2 (sinEnvelopeHVector d θ₂)‖ =
        ‖WithLp.toLp 2 (sinEnvelopeHVector d θ₂) - WithLp.toLp 2 (sinEnvelopeHVector d θ₁)‖
      exact norm_sub_rev _ _
    rw [hn, abs_of_nonneg (by linarith)]
    exact hp

private theorem sin_envelope_fg_lipschitz_sq (d x y : ℝ) (hd : 0 < d) :
    (sinEnvelopeFilterF d x-sinEnvelopeFilterF d y)^2 +
      (sinEnvelopeFilterG d x-sinEnvelopeFilterG d y)^2 ≤ (1/d)^2*(x-y)^2 := by
  have h := sin_envelope_h_lipschitz d x y hd
  have hp : 0 ≤ (1/d)*|x-y| := by positivity
  have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) hp).mpr h
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)), mul_pow, sq_abs] at hsq
  simp [Fin.sum_univ_succ, sinEnvelopeHVector, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, sq_abs] at hsq
  rw [show (1/d)^2 = (d^2)⁻¹ by ring]
  nlinarith [sq_nonneg (Real.sqrt (1-sinEnvelopeFilterF d x^2-sinEnvelopeFilterG d x^2) -
    Real.sqrt (1-sinEnvelopeFilterF d y^2-sinEnvelopeFilterG d y^2))]

private theorem sin_envelope_low_mass (d x : ℝ) (hd : 0 < d) (hx : x ≤ 2*d) :
    sinEnvelopeFilterF d x^2+sinEnvelopeFilterG d x^2 = (1/4 : ℝ) := by
  by_cases he : x = 2*d
  · rw [he, (sin_envelope_filter_branch_values d hd).1,
      (sin_envelope_filter_branch_values d hd).2.1]
    norm_num
  · have hw : ¬ 2*d ≤ x := by intro h; exact he (le_antisymm hx h)
    unfold sinEnvelopeFilterF sinEnvelopeFilterG
    simp only [if_neg hw]
    split_ifs with h
    · nlinarith [Real.sin_sq_add_cos_sq (Real.pi/2*(x-d)/d)]
    · norm_num

theorem sin_envelope_filter_stability_global (d x y : ℝ) (hd : 0 < d) :
    (sinEnvelopeFilterF d x-sinEnvelopeFilterF d y)^2 +
      (sinEnvelopeFilterG d x-sinEnvelopeFilterG d y)^2 ≤
      2*Real.pi^2*(1/(2*d))^2*(x-y)^2*
        (sinEnvelopeFilterF d x^2+sinEnvelopeFilterG d x^2) := by
  have hpi : 8 ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three]
  by_cases hx : x ≤ 2*d
  · rw [sin_envelope_low_mass d x hd hx]
    have h := sin_envelope_fg_lipschitz_sq d x y hd
    have he : 2*Real.pi^2*(1/(2*d))^2*(x-y)^2*(1/4) =
        (Real.pi^2/8)*((1/d)^2*(x-y)^2) := by ring
    rw [he]
    exact h.trans (le_mul_of_one_le_left (by positivity) (by linarith))
  · have hxx : 2*d ≤ x := by linarith
    have hx0 : 0 < x := by linarith
    have hf : 0 ≤ d/x := div_nonneg hd.le hx0.le
    have hf' : d/x ≤ 1/2 := (div_le_iff₀ hx0).mpr (by linarith)
    have he : 2*Real.pi^2*(1/(2*d))^2*(x-y)^2*(d/x)^2 =
        (Real.pi^2/2)*((x-y)/x)^2 := by
      field_simp
    rw [show sinEnvelopeFilterF d x = d/x by simp [sinEnvelopeFilterF, hxx],
      show sinEnvelopeFilterG d x = 0 by simp [sinEnvelopeFilterG, hxx], zero_pow (by decide),
      add_zero, he]
    by_cases hy : 2*d ≤ y
    · have hy0 : 0 < y := by linarith
      have hg : 0 ≤ d/y := div_nonneg hd.le hy0.le
      have hg' : d/y ≤ 1/2 := (div_le_iff₀ hy0).mpr (by linarith)
      rw [show sinEnvelopeFilterF d y = d/y by simp [sinEnvelopeFilterF, hy],
        show sinEnvelopeFilterG d y = 0 by simp [sinEnvelopeFilterG, hy]]
      have hdiff : (d/x-d/y)^2 = (d/y)^2*((x-y)/x)^2 := by
        field_simp
        all_goals ring
      norm_num only [sub_self, zero_pow (by decide : (2:ℕ) ≠ 0), add_zero]
      rw [hdiff]
      exact mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
    · by_cases hl : d ≤ y
      · have hv := sin_envelope_ramp_values d y hd hl (by linarith)
        rw [hv.1, hv.2]
        let a := x/(2*d)-1
        let v := (2*d-y)/(2*d)
        let u := a+1
        have ha : 0 ≤ a := by
          dsimp [a]
          have hh : (1:ℝ) ≤ x/(2*d) :=
            (le_div_iff₀ (by positivity : 0 < 2*d)).mpr (by linarith)
          linarith
        have hv0 : 0 ≤ v := div_nonneg (by linarith) (by positivity)
        have hv1 : v ≤ 1/2 := (div_le_iff₀ (by positivity)).mpr (by linarith)
        have hu : 0 < u := by dsimp [u]; linarith
        have hr : d/x = 1/(2*u) := by
          dsimp [u,a]
          field_simp [hx0.ne', hd.ne']
          all_goals ring
        have hgap : (x-y)/x = (a+v)/u := by
          dsimp [u,a,v]
          field_simp [hx0.ne', hd.ne']
          all_goals ring
        have hang : Real.pi/2*(y-d)/d = Real.pi/2 - Real.pi*v := by
          dsimp [v]
          field_simp [hd.ne']
          all_goals ring
        have hsin : Real.sin (Real.pi/2*(y-d)/d) = Real.cos (Real.pi*v) := by
          rw [hang, Real.sin_pi_div_two_sub]
        have hcos := Real.one_sub_sq_div_two_le_cos (x := Real.pi*v)
        have hupper : (d/x-(1/2)*Real.sin (Real.pi/2*(y-d)/d))^2 +
            (0-(1/2)*Real.cos (Real.pi/2*(y-d)/d))^2 ≤
              (d/x-1/2)^2+(d/x)*(Real.pi*v)^2/2 := by
          have ht := Real.sin_sq_add_cos_sq (Real.pi/2*(y-d)/d)
          rw [hsin] at ht ⊢
          nlinarith [mul_nonneg hf (show 0 ≤ Real.cos (Real.pi*v)-1+(Real.pi*v)^2/2 by linarith)]
        have hform : (d/x-1/2)^2+(d/x)*(Real.pi*v)^2/2 =
            (a^2+Real.pi^2*u*v^2)/(4*u^2) := by
          rw [hr]
          dsimp [u]
          field_simp
          all_goals ring
        have huv : u*v^2 ≤ (a+v)^2 := by
          dsimp [u]
          have hv2 : 0 ≤ 2-v := by linarith
          nlinarith [mul_nonneg ha (mul_nonneg hv0 hv2)]
        have ha2 : a^2 ≤ (a+v)^2 := by nlinarith
        have hpoly : a^2+Real.pi^2*u*v^2 ≤ 2*Real.pi^2*(a+v)^2 := by
          have hp := mul_le_mul_of_nonneg_left huv (sq_nonneg Real.pi)
          have hn := mul_nonneg (show 0 ≤ Real.pi^2-1 by linarith) (sq_nonneg (a+v))
          nlinarith
        have htarget : (Real.pi^2/2)*((x-y)/x)^2 =
            (2*Real.pi^2*(a+v)^2)/(4*u^2) := by rw [hgap]; ring
        rw [htarget]
        exact hupper.trans (hform ▸ div_le_div_of_nonneg_right hpoly (by positivity))
      · rw [show sinEnvelopeFilterF d y = 0 by simp [sinEnvelopeFilterF, hy, hl],
          show sinEnvelopeFilterG d y = 1/2 by simp [sinEnvelopeFilterG, hy, hl]]
        have hgap : 1/2 ≤ (x-y)/x := (le_div_iff₀ hx0).mpr (by linarith)
        have hsq : (1/4 : ℝ) ≤ ((x-y)/x)^2 := by nlinarith
        have hm := mul_le_mul_of_nonneg_left hsq (show 0 ≤ Real.pi^2/2 by positivity)
        nlinarith

end Qatlib.Concepts.HhlErrorBridge.FilterStability
