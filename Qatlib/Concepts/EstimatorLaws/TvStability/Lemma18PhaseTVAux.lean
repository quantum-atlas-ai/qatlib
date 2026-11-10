/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
import Mathlib.Analysis.Calculus.Deriv.MeanValue
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

namespace Qatlib.Concepts.EstimatorLaws.TvStability

open Matrix Set
open scoped Classical BigOperators

theorem phaseDistance_le_half (x y : ℝ) : phaseDistance x y ≤ 1 / 2 := by
  unfold phaseDistance
  have hl := Int.floor_le (x - y + 1 / 2)
  have hu := Int.lt_floor_add_one (x - y + 1 / 2)
  apply abs_le.mpr
  constructor <;> linarith

private theorem sin_lower_cubic (x : ℝ) (hx : 0 ≤ x) : x - x ^ 3 / 6 ≤ Real.sin x := by
  let f := fun t : ℝ => Real.sin t - t + t ^ 3 / 6
  have hd (t : ℝ) : HasDerivAt f (Real.cos t - 1 + t ^ 2 / 2) t := by
    convert! ((Real.hasDerivAt_sin t).sub (hasDerivAt_id t)).add
      (((hasDerivAt_id t).pow 3).div_const 6) using 1
    all_goals simp only [id_eq]
    all_goals ring
  have hm : Monotone f := monotone_of_deriv_nonneg
    (fun t => (hd t).differentiableAt)
    (fun t => by rw [(hd t).deriv]; linarith [Real.one_sub_sq_div_two_le_cos (x := t)])
  have h := hm hx
  have hh : 0 ≤ Real.sin x - x + x ^ 3 / 6 := by simpa [f] using! h
  linarith

theorem sinc_square_defect_le (x : ℝ) (hx : 0 < x) :
    1 - (Real.sin x / x) ^ 2 ≤ x ^ 2 / 3 := by
  by_cases hlarge : 3 ≤ x ^ 2
  · nlinarith [sq_nonneg (Real.sin x / x)]
  have hl := sin_lower_cubic x hx.le
  have hratio : 1 - x ^ 2 / 6 ≤ Real.sin x / x := by
    apply (le_div_iff₀ hx).mpr
    nlinarith
  have hlow : 0 ≤ 1 - x ^ 2 / 6 := by linarith
  have hsq := pow_le_pow_left₀ hlow hratio 2
  nlinarith [sq_nonneg (x ^ 2)]

private theorem exp_phase_conjugate (w : ℂ) (hw : w.re = 0) :
    (starRingEnd ℂ) (Complex.exp w) = Complex.exp (-w) := by
  rw [← Complex.exp_conj]
  congr 1
  apply Complex.ext <;> simp [hw]

theorem offGridPhase_inner_eq_kernel_zero (M : ℕ) (hM : 0 < M) (x y : ℝ) :
    Inner (offGridPhase M x) (offGridPhase M y) = qpeKernel M (y - x) ⟨0, hM⟩ := by
  rw [inner_apply, (offgrid_phase_kernel_formula M (y - x) ⟨0, hM⟩ hM).2.1]
  simp only [Nat.cast_zero, Complex.ofReal_zero, zero_div, sub_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [offGridPhase_apply, offGridPhase_apply, map_mul, map_inv₀, Complex.conj_ofReal,
    exp_phase_conjugate _ (by simp [Complex.mul_re, Complex.mul_im])]
  calc
    _ = (Real.sqrt (M : ℝ) : ℂ)⁻¹ *
        (Complex.exp (-(2 * Real.pi * Complex.I * ((j.val : ℝ) * x))) *
          Complex.exp (2 * Real.pi * Complex.I * ((j.val : ℝ) * y))) *
        (Real.sqrt (M : ℝ) : ℂ)⁻¹ := by ring
    _ = (M : ℂ)⁻¹ *
        (Complex.exp (-(2 * Real.pi * Complex.I * ((j.val : ℝ) * x))) *
          Complex.exp (2 * Real.pi * Complex.I * ((j.val : ℝ) * y))) := mul_inv_sqrt M hM _
    _ = _ := by
      rw [← Complex.exp_add]
      congr 1
      congr 1
      push_cast
      ring

theorem norm_exp_two_pi_sub_one (t : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * t) - 1‖ = 2 * |Real.sin (Real.pi * t)| := by
  have he : (2 * Real.pi * Complex.I * t : ℂ) = Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he, Complex.norm_exp_I_mul_ofReal_sub_one,
    show (2 * Real.pi * t) / 2 = Real.pi * t by ring, Real.norm_eq_abs, abs_mul]
  norm_num

private theorem abs_sin_mul_abs (a r : ℝ) :
    |Real.sin (a * |r|)| = |Real.sin (a * r)| := by
  rcases le_or_gt 0 r with hr | hr
  · rw [abs_of_nonneg hr]
  · rw [abs_of_neg hr, mul_neg, Real.sin_neg, abs_neg]

theorem offGridPhase_inner_norm_dirichlet (M : ℕ) (hM : 0 < M) (x y : ℝ)
    (hδ : 0 < phaseDistance x y) :
    ‖Inner (offGridPhase M x) (offGridPhase M y)‖ =
      |Real.sin (Real.pi * M * phaseDistance x y)| /
        ((M : ℝ) * Real.sin (Real.pi * phaseDistance x y)) := by
  let c : ℤ := ⌊x - y + 1 / 2⌋
  let r : ℝ := x - y - (c : ℝ)
  let φ : ℝ := -r
  let z : Fin M := ⟨0, hM⟩
  have hφ : |φ| = phaseDistance x y := by simp only [φ, abs_neg]; rfl
  have hperiod : qpeKernel M (y - x) z = qpeKernel M φ z := by
    have he : y - x = φ + ((-c : ℤ) : ℝ) := by dsimp [φ, r]; push_cast; ring
    rw [he, qpeKernel_int_add]
  have hsin : 0 < Real.sin (Real.pi * phaseDistance x y) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hδ)
      (by nlinarith [phaseDistance_le_half x y, Real.pi_pos])
  have hden : |Real.sin (Real.pi * φ)| = Real.sin (Real.pi * phaseDistance x y) := by
    rw [← abs_sin_mul_abs, hφ, abs_of_pos hsin]
  have hnum : |Real.sin (Real.pi * ((M : ℝ) * φ))| =
      |Real.sin (Real.pi * M * phaseDistance x y)| := by
    rw [← mul_assoc, ← abs_sin_mul_abs, hφ]
  have hg := congrArg norm (qpeKernel_geometric_identity M φ z hM)
  simp only [z, Nat.cast_zero, Complex.ofReal_zero, zero_div, sub_zero, norm_mul,
    Complex.norm_natCast] at hg
  have hnormM : ‖Complex.exp (2 * Real.pi * Complex.I * ((M : ℂ) * (φ : ℂ))) - 1‖ =
      2 * |Real.sin (Real.pi * ((M : ℝ) * φ))| := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_natCast] using!
      norm_exp_two_pi_sub_one ((M : ℝ) * φ)
  simp only [Complex.ofReal_natCast] at hg
  rw [norm_exp_two_pi_sub_one φ, hnormM, hden, hnum] at hg
  rw [offGridPhase_inner_eq_kernel_zero M hM x y, hperiod]
  apply (eq_div_iff (mul_ne_zero (by exact_mod_cast hM.ne') hsin.ne')).mpr
  linear_combination (1 / 2 : ℝ) * hg

end Qatlib.Concepts.EstimatorLaws.TvStability
