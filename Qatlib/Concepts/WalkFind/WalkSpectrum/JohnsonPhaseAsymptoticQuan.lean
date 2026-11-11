/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.WalkSpectrum.JohnsonPhaseAsymptoticStat
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Asymptotics of Johnson-walk eigenphases

This module proves a half-angle identity expressing `arccos (1-2*a)` through `arcsin (sqrt a)`.
It uses the derivative of arcsine at zero to establish the Johnson-walk phase asymptotic in
[Ambainis2007ElementDistinctness].

For fixed positive `j`, along sequences with `N` and `r` tending to infinity and `r/N` tending
to zero, the phase divided by `2*sqrt (j/r)` tends to one.

## Main statements

* `arccos_half_angle`: the inverse-trigonometric half-angle identity.
* `johnsonPhaseAsymptotic_answer`: the normalized eigenphase limit.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.WalkFind.SearchAlgorithm

set_option autoImplicit false

namespace Qatlib.Concepts.WalkFind.WalkSpectrum
open Filter
open scoped Topology

/-- For `0 ≤ a ≤ 1`, `arccos (1-2*a)` equals `2*arcsin (sqrt a)`. -/
private theorem arccos_half_angle (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    Real.arccos (1-2*a) = 2*Real.arcsin (Real.sqrt a) := by
  have hs1 := Real.sqrt_le_one.mpr ha1
  have hsin := Real.sin_arcsin (by linarith [Real.sqrt_nonneg a] : -1 ≤ Real.sqrt a) hs1
  have hcos : Real.cos (2*Real.arcsin (Real.sqrt a)) = 1-2*a := by
    rw [Real.cos_two_mul]
    have hid := Real.sin_sq_add_cos_sq (Real.arcsin (Real.sqrt a))
    rw [hsin, Real.sq_sqrt ha] at hid
    linarith
  rw [← hcos, Real.arccos_cos]
  · linarith [Real.arcsin_nonneg.mpr (Real.sqrt_nonneg a)]
  · linarith [Real.arcsin_le_pi_div_two (Real.sqrt a)]

/-- The Johnson eigenphase satisfies `JohnsonPhaseAsymptotic`: for fixed positive `j`, its ratio
to `2*sqrt (j/r)` tends to one as `N,r` tend to infinity with `r/N` tending to zero
[Ambainis2007ElementDistinctness]. -/
theorem johnsonPhaseAsymptotic_answer : JohnsonPhaseAsymptotic := by
  intro j hj N r hN hr hsmall
  let L : ℕ → ℝ := fun n =>
    (1+(1-(j : ℝ))/(N n : ℝ))/((1+1/(r n : ℝ))*(1-(r n : ℝ)/(N n : ℝ)))
  let a : ℕ → ℝ := fun n => (j : ℝ)/(r n : ℝ)*L n
  have hNi := tendsto_inv_atTop_zero.comp hN
  have hri := tendsto_inv_atTop_zero.comp hr
  have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hnum : Tendsto (fun n => 1+(1-(j : ℝ))/(N n : ℝ)) atTop (nhds 1) := by
    simpa [div_eq_mul_inv] using! tendsto_const_nhds.add
      (tendsto_const_nhds.mul hNi)
  have hden : Tendsto (fun n => (1+1/(r n : ℝ))*(1-(r n : ℝ)/(N n : ℝ)))
      atTop (nhds 1) := by
    simpa [one_div] using! (hc.add hri).mul (hc.sub hsmall)
  have hL : Tendsto L atTop (nhds 1) := by
    simpa [L] using! hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
  have ha : Tendsto a atTop (nhds 0) := by
    simpa [a, div_eq_mul_inv] using! (tendsto_const_nhds.mul hri).mul hL
  have hposN : ∀ᶠ n in atTop, 0 < (N n : ℝ) := hN.eventually (eventually_gt_atTop 0)
  have hposr : ∀ᶠ n in atTop, 0 < (r n : ℝ) := hr.eventually (eventually_gt_atTop 0)
  have hposL : ∀ᶠ n in atTop, 0 < L n := hL.eventually (eventually_gt_nhds (by norm_num))
  have hposa : ∀ᶠ n in atTop, 0 < a n := by
    filter_upwards [hposr, hposL] with n hn hl
    exact mul_pos (div_pos (by exact_mod_cast hj) hn) hl
  have hasqrt : Tendsto (fun n => Real.sqrt (a n)) atTop (nhds 0) := by
    simpa using! ha.sqrt
  have hright : Tendsto (fun n => Real.sqrt (a n)) atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hasqrt, hposa.mono fun _ hn => Real.sqrt_pos.mpr hn⟩
  have hderiv : HasDerivAt Real.arcsin 1 0 := by
    simpa using! Real.hasDerivAt_arcsin (by norm_num : (0 : ℝ) ≠ -1)
      (by norm_num : (0 : ℝ) ≠ 1)
  have hquot : Tendsto (fun n => Real.arcsin (Real.sqrt (a n))/Real.sqrt (a n))
      atTop (nhds 1) := by
    simpa [Real.arcsin_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using!
      hderiv.tendsto_slope_zero_right.comp hright
  have hresult : Tendsto (fun n =>
      (Real.arcsin (Real.sqrt (a n))/Real.sqrt (a n))*Real.sqrt (L n))
      atTop (nhds 1) := by
    simpa using! hquot.mul hL.sqrt
  apply hresult.congr'
  have hale : ∀ᶠ n in atTop, a n ≤ 1 :=
    (ha.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))).mono fun _ h => h.le
  have hnr : ∀ᶠ n in atTop, (r n : ℝ)/(N n : ℝ) < 1 :=
    hsmall.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hposN, hposr, hposL, hposa, hale, hnr] with n hn hrn hl hap hal hnrn
  have hdiff : (N n : ℝ)-(r n : ℝ) ≠ 0 := by
    have hh := (div_lt_one hn).mp hnrn
    linarith
  have heq : (j : ℝ)*(N n+1-j)/((r n+1)*(N n-r n)) = a n := by
    dsimp [a, L]
    field_simp
    ring
  have hs : Real.sqrt (a n) = Real.sqrt ((j : ℝ)/(r n : ℝ))*Real.sqrt (L n) := by
    exact Real.sqrt_mul (by positivity) _
  have hsne : Real.sqrt ((j : ℝ)/(r n : ℝ)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr
    (div_pos (by exact_mod_cast hj) hrn))
  have hlne : Real.sqrt (L n) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hl)
  change _ = johnsonPhase j (N n) (r n)/(2*Real.sqrt ((j : ℝ)/(r n : ℝ)))
  unfold johnsonPhase
  rw [show 1-2*(j : ℝ)*(N n+1-j)/((r n+1)*(N n-r n)) = 1-2*a n by rw [← heq]; ring,
    arccos_half_angle (a n) hap.le hal, hs]
  field_simp

end Qatlib.Concepts.WalkFind.WalkSpectrum
