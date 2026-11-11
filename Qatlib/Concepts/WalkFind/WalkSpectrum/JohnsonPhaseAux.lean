/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Elementary bounds for Johnson-walk phases

This module expresses the complex diffusion phase using `2*arcsin (sqrt e)` and bounds that
angle in terms of `sqrt e`. It also converts chordal distance on the unit circle into a
controlled additive phase displacement, providing estimates for the Johnson-walk spectral
analysis [Ambainis2007ElementDistinctness].

## Main statements

* `jw_diffusion_phase_exp`: the diffusion phase as a complex exponential.
* `jw_unit_circle_phase_transport`: a phase displacement bounded by chordal distance.
* `jw_arcsin_sqrt_bounds`: explicit square-root bounds for the half-angle.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.WalkFind.WalkSpectrum

/-- For `0 ≤ e ≤ 1`, the complex number `1-2*e + 2*i*sqrt (e-e²)` equals `exp (i*(2*arcsin (sqrt
e)))`. -/
theorem jw_diffusion_phase_exp (e : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1) :
    (1 - 2 * e : ℂ) + Complex.I * (2 * Real.sqrt (e - e * e) : ℝ) =
      Complex.exp (Complex.I * (2 * Real.arcsin (Real.sqrt e) : ℝ)) := by
  have hs : 0 ≤ Real.sqrt e := Real.sqrt_nonneg e
  have hs1 : Real.sqrt e ≤ 1 := (Real.sqrt_le_one).mpr he1
  have hsin := Real.sin_arcsin (by linarith : -1 ≤ Real.sqrt e) hs1
  have hcos := Real.cos_arcsin (Real.sqrt e)
  have hsq := Real.sq_sqrt he
  have hmul : Real.sqrt e * Real.sqrt (1 - e) = Real.sqrt (e - e * e) := by
    rw [← Real.sqrt_mul he]
    congr 1
    ring
  have hcd : Real.cos (2 * Real.arcsin (Real.sqrt e)) = 1 - 2 * e := by
    rw [Real.cos_two_mul', hsin, hcos, hsq, Real.sq_sqrt (by linarith : 0 ≤ 1 - e)]
    ring
  have hsd : Real.sin (2 * Real.arcsin (Real.sqrt e)) = 2 * Real.sqrt (e - e * e) := by
    rw [Real.sin_two_mul, hsin, hcos, hsq]
    nlinarith [hmul]
  rw [mul_comm Complex.I (↑(2 * Real.arcsin (Real.sqrt e))),
    Complex.exp_ofReal_mul_I, hcd, hsd]
  push_cast
  ring

/-- For a unit complex number `z` and reference phase `θ`, there is a phase displacement `a`
representing `z` with `|a|` at most `π/2` times its chordal distance from `exp (i*θ)`. -/
theorem jw_unit_circle_phase_transport (z : ℂ) (hz : ‖z‖ = 1) (θ : ℝ) :
    ∃ a : ℝ, |a| ≤ Real.pi / 2 * ‖z - Complex.exp (Complex.I * θ)‖ ∧
      z = Complex.exp (Complex.I * (θ + a : ℝ)) := by
  let q := z * Complex.exp (Complex.I * (-θ : ℝ))
  have hqn : ‖q‖ = 1 := by
    dsimp only [q]
    rw [norm_mul, hz, Complex.norm_exp_I_mul_ofReal, mul_one]
  have hq : Complex.exp (Complex.I * (q.arg : ℝ)) = q := by
    have h := Complex.norm_mul_exp_arg_mul_I q
    rw [hqn] at h
    simpa [mul_comm] using h
  have hprod : Complex.exp (Complex.I * θ) * Complex.exp (Complex.I * (-θ : ℝ)) = 1 := by
    rw [← Complex.exp_add]
    simp
  have hqd : q - 1 = (z - Complex.exp (Complex.I * θ)) * Complex.exp (Complex.I * (-θ : ℝ)) := by
    rw [sub_mul, hprod]
  have hnorm : ‖q - 1‖ = ‖z - Complex.exp (Complex.I * θ)‖ := by
    rw [hqd, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
  have harg := Complex.abs_arg_le_pi q
  have hs := Real.mul_abs_le_abs_sin
    (show |q.arg / 2| ≤ Real.pi / 2 by rw [abs_div]; norm_num; linarith)
  have hc := Complex.norm_exp_I_mul_ofReal_sub_one q.arg
  rw [hq, hnorm] at hc
  rw [abs_div] at hs
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hs
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hc
  refine ⟨q.arg, ?_, ?_⟩
  · have hp := mul_le_mul_of_nonneg_left hs Real.pi_pos.le
    field_simp at hp
    nlinarith [Real.pi_pos]
  · have hmul := congrArg (fun x => x * Complex.exp (Complex.I * θ)) hq
    try dsimp only at hmul
    have hr : q * Complex.exp (Complex.I * θ) = z := by
      dsimp [q]
      rw [mul_assoc, mul_comm (Complex.exp (Complex.I * (-θ : ℝ))), hprod, mul_one]
    rw [hr] at hmul
    calc
      z = Complex.exp (Complex.I * (q.arg : ℝ)) * Complex.exp (Complex.I * θ) := hmul.symm
      _ = Complex.exp (Complex.I * (θ + q.arg : ℝ)) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring

/-- For `0 ≤ e ≤ 1/2`, `arcsin (sqrt e)` lies between `sqrt e` and `(6/5)*sqrt e`. -/
theorem jw_arcsin_sqrt_bounds (e : ℝ) (he : 0 ≤ e) (hehalf : e ≤ 1 / 2) :
    Real.sqrt e ≤ Real.arcsin (Real.sqrt e) ∧
      Real.arcsin (Real.sqrt e) ≤ 6 / 5 * Real.sqrt e := by
  have hs : 0 ≤ Real.sqrt e := Real.sqrt_nonneg e
  have hs1 : Real.sqrt e ≤ 1 := (Real.sqrt_le_one).mpr (by linarith)
  have ht0 : 0 ≤ Real.arcsin (Real.sqrt e) := Real.arcsin_nonneg.mpr hs
  have hsin := Real.sin_arcsin (by linarith : -1 ≤ Real.sqrt e) hs1
  have ht : Real.arcsin (Real.sqrt e) ≤ Real.pi / 4 := by
    have hss : Real.sqrt e ≤ Real.sqrt 2 / 2 := by
      have hsq := Real.sq_sqrt he
      have hsq2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      nlinarith [Real.sqrt_nonneg 2]
    rw [← Real.arcsin_sin (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ Real.pi / 4)
      (by linarith [Real.pi_pos] : Real.pi / 4 ≤ Real.pi / 2)]
    exact Real.arcsin_le_arcsin (by simpa only [Real.sin_pi_div_four] using hss)
  constructor
  · simpa only [hsin] using Real.sin_le ht0
  · by_cases hzero : Real.arcsin (Real.sqrt e) = 0
    · rw [hzero]; positivity
    have htp : 0 < Real.arcsin (Real.sqrt e) := lt_of_le_of_ne ht0 (Ne.symm hzero)
    have h : Real.arcsin (Real.sqrt e) - Real.arcsin (Real.sqrt e) ^ 3 / 4 < Real.sin (Real.arcsin (Real.sqrt e)) := by
      linarith [Real.sin_gt_sub_cube htp, pow_nonneg htp.le 3]
    rw [hsin] at h
    have htsq : Real.arcsin (Real.sqrt e) ^ 2 ≤ 2 / 3 := by
      nlinarith [Real.pi_lt_d2, sq_nonneg (Real.pi / 4 - Real.arcsin (Real.sqrt e))]
    have hc := mul_nonneg ht0 (sub_nonneg.mpr htsq)
    nlinarith

end Qatlib.Concepts.WalkFind.WalkSpectrum
