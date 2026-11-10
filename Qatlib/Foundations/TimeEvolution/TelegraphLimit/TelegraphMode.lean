/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.TimeEvolution.TelegraphLimit.TelegraphRates
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Qatlib.Foundations.TimeEvolution.TelegraphLimit

def heatMode (a t : ℝ) : ℝ := Real.exp (-a*t)

def mode (δ a t : ℝ) : ℝ :=
  (1+coeff δ a)*Real.exp (-slow δ a*t)-coeff δ a*Real.exp (-fast δ a*t)

def modeDeriv (δ a t : ℝ) : ℝ :=
  -(1+coeff δ a)*slow δ a*Real.exp (-slow δ a*t)+coeff δ a*fast δ a*Real.exp (-fast δ a*t)

def modeDeriv2 (δ a t : ℝ) : ℝ :=
  (1+coeff δ a)*(slow δ a)^2*Real.exp (-slow δ a*t)-coeff δ a*(fast δ a)^2*Real.exp (-fast δ a*t)

theorem mode_hasDerivAt (δ a t : ℝ) : HasDerivAt (mode δ a) (modeDeriv δ a t) t := by
  have hg := ((hasDerivAt_id t).const_mul (-slow δ a)).exp.const_mul (1+coeff δ a)
  have hf := ((hasDerivAt_id t).const_mul (-fast δ a)).exp.const_mul (coeff δ a)
  convert! hg.sub hf using 1
  try dsimp [mode,modeDeriv]
  ring

theorem modeDeriv_hasDerivAt (δ a t : ℝ) : HasDerivAt (modeDeriv δ a) (modeDeriv2 δ a t) t := by
  have hg := ((hasDerivAt_id t).const_mul (-slow δ a)).exp.const_mul (-(1+coeff δ a)*slow δ a)
  have hf := ((hasDerivAt_id t).const_mul (-fast δ a)).exp.const_mul (coeff δ a*fast δ a)
  convert! hg.add hf using 1
  try dsimp [modeDeriv,modeDeriv2]
  ring

theorem mode_solves {δ a : ℝ} (hδ : 0<δ) (ha : 0≤a) (hm : 4*δ*a≤3/4) (t : ℝ) :
    δ*modeDeriv2 δ a t+modeDeriv δ a t+a*mode δ a t=0 ∧
    mode δ a 0=1 ∧ modeDeriv δ a 0=0 := by
  obtain ⟨hg,hf⟩ := characteristic hδ ha hm
  have hi := zero_initial_flux hδ ha hm
  refine ⟨?_,?_,?_⟩
  · dsimp [modeDeriv2,modeDeriv,mode]
    linear_combination (1+coeff δ a)*Real.exp (-slow δ a*t)*hg-coeff δ a*Real.exp (-fast δ a*t)*hf
  · simp [mode]
  · simp [modeDeriv]
    linarith

theorem decay_perturbation {a g t : ℝ} (hag : a≤g) (ht : 0≤t) :
    |Real.exp (-g*t)-Real.exp (-a*t)|≤(g-a)*t*Real.exp (-a*t) := by
  have hle : Real.exp (-g*t)≤Real.exp (-a*t) := Real.exp_le_exp.mpr (by nlinarith)
  rw [abs_of_nonpos (sub_nonpos.mpr hle)]
  have he := Real.add_one_le_exp (-(g-a)*t)
  have hi : Real.exp (-g*t)=Real.exp (-a*t)*Real.exp (-(g-a)*t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hi]
  nlinarith [mul_nonneg (Real.exp_pos (-a*t)).le (show 0≤Real.exp (-(g-a)*t)-(-(g-a)*t+1) by linarith)]

theorem mode_error {δ a t : ℝ} (hδ : 0<δ) (ha : 0≤a) (hm : 4*δ*a≤3/4) (ht : 0≤t) :
    |mode δ a t-heatMode a t|≤(4*δ*a+4*δ*a^2*t)*heatMode a t := by
  obtain ⟨hag,hgf,hc0,hc,hgap⟩ := rate_bounds hδ ha hm
  let G := Real.exp (-slow δ a*t)
  let F := Real.exp (-fast δ a*t)
  let H := Real.exp (-a*t)
  have hFG : F≤G := Real.exp_le_exp.mpr (by nlinarith)
  have hGH : G≤H := Real.exp_le_exp.mpr (by nlinarith)
  have hF0 : 0≤F := (Real.exp_pos _).le
  have hH0 : 0≤H := (Real.exp_pos _).le
  have he := decay_perturbation hag ht
  change |G-H|≤(slow δ a-a)*t*H at he
  change |(1+coeff δ a)*G-coeff δ a*F-H|≤(4*δ*a+4*δ*a^2*t)*H
  calc
    |(1+coeff δ a)*G-coeff δ a*F-H|=|(G-H)+coeff δ a*(G-F)| := by congr 1;ring
    _≤|G-H|+|coeff δ a*(G-F)| := abs_add_le _ _
    _≤(slow δ a-a)*t*H+coeff δ a*H := by
      apply add_le_add he
      rw [abs_mul,abs_of_nonneg hc0,abs_of_nonneg (sub_nonneg.mpr hFG)]
      exact mul_le_mul_of_nonneg_left (by linarith) hc0
    _≤(4*δ*a+4*δ*a^2*t)*H := by
      have hg := mul_le_mul_of_nonneg_right hgap (mul_nonneg ht hH0)
      have hc' := mul_le_mul_of_nonneg_right hc hH0
      nlinarith
end Qatlib.Foundations.TimeEvolution.TelegraphLimit
