/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.TimeEvolution.TelegraphLimit.TelegraphRates
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Telegraph modes and their heat-mode error

This module defines a scalar telegraph mode as a combination of slow and fast exponentials,
together with its first two derivatives. Under the stated rate restrictions, `mode_solves`
verifies the telegraph differential equation with initial value one and initial derivative zero.

The estimate `mode_error` compares this mode with the heat exponential at nonnegative times,
using the perturbation bound `decay_perturbation`.

The mathematical background is discussed in [JinLiu2024].

## Main statements

* `mode_solves`: verifies the differential equation and initial conditions.
* `decay_perturbation`: compares exponential decay at ordered rates.
* `mode_error`: bounds the scalar telegraph-to-heat difference.

## References

* [Jin and Liu, 2024][JinLiu2024]
-/

set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Qatlib.Foundations.TimeEvolution.TelegraphLimit

/-- The scalar heat multiplier `exp (-a * t)`. -/
def heatMode (a t : ℝ) : ℝ := Real.exp (-a*t)

/-- The telegraph multiplier `(1 + coeff δ a) * exp (-slow δ a * t) - coeff δ a * exp (-fast δ a
* t)`. -/
def mode (δ a t : ℝ) : ℝ :=
  (1+coeff δ a)*Real.exp (-slow δ a*t)-coeff δ a*Real.exp (-fast δ a*t)

/-- The explicit first time derivative of the telegraph multiplier, obtained by differentiating
its two exponential terms. -/
def modeDeriv (δ a t : ℝ) : ℝ :=
  -(1+coeff δ a)*slow δ a*Real.exp (-slow δ a*t)+coeff δ a*fast δ a*Real.exp (-fast δ a*t)

/-- The explicit second time derivative of the telegraph multiplier, with each exponential
weighted by its squared decay rate. -/
def modeDeriv2 (δ a t : ℝ) : ℝ :=
  (1+coeff δ a)*(slow δ a)^2*Real.exp (-slow δ a*t)-coeff δ a*(fast δ a)^2*Real.exp (-fast δ a*t)

/-- The time derivative of `mode δ a` at `t` is `modeDeriv δ a t`. -/
theorem mode_hasDerivAt (δ a t : ℝ) : HasDerivAt (mode δ a) (modeDeriv δ a t) t := by
  have hg := ((hasDerivAt_id t).const_mul (-slow δ a)).exp.const_mul (1+coeff δ a)
  have hf := ((hasDerivAt_id t).const_mul (-fast δ a)).exp.const_mul (coeff δ a)
  convert! hg.sub hf using 1
  try dsimp [mode,modeDeriv]
  ring

/-- The time derivative of `modeDeriv δ a` at `t` is `modeDeriv2 δ a t`. -/
theorem modeDeriv_hasDerivAt (δ a t : ℝ) : HasDerivAt (modeDeriv δ a) (modeDeriv2 δ a t) t := by
  have hg := ((hasDerivAt_id t).const_mul (-slow δ a)).exp.const_mul (-(1+coeff δ a)*slow δ a)
  have hf := ((hasDerivAt_id t).const_mul (-fast δ a)).exp.const_mul (coeff δ a*fast δ a)
  convert! hg.add hf using 1
  try dsimp [modeDeriv,modeDeriv2]
  ring

/-- For positive `δ`, nonnegative `a`, and `4 * δ * a ≤ 3/4`, the mode satisfies `δ * modeDeriv2
+ modeDeriv + a * mode = 0` with initial value one and initial derivative zero. -/
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

/-- For `a ≤ g` and nonnegative time, the difference of their decay exponentials is at most `(g
- a) * t * exp (-a * t)`. -/
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

/-- For positive `δ`, nonnegative rate and time, and `4 * δ * a ≤ 3/4`, the telegraph-to-heat
error is at most `(4 * δ * a + 4 * δ * a ^ 2 * t) * heatMode a t`. -/
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
