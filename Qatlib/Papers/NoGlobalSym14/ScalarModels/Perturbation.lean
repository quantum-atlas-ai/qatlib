/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

set_option autoImplicit false

namespace Qatlib.Papers.NoGlobalSym14.ScalarModels

noncomputable def gammaC1 (k : ℝ) : ℝ := 1 / k

noncomputable def gammaC2 (k N μ : ℝ) : ℝ := 1 / k + 1 / ((N - 1) * μ)

theorem case1_critical_gamma_degenerate (k : ℝ) (hk : k ≠ 0) :
    -(gammaC1 k) * k = -1 := by
  unfold gammaC1
  field_simp

theorem case2_critical_gamma_excess (k N μ : ℝ) :
    gammaC2 k N μ - 1 / k = 1 / ((N - 1) * μ) := by
  unfold gammaC2
  rw [add_sub_cancel_left]

noncomputable def case1Eplus (N : ℝ) : ℝ := -1 + 1 / Real.sqrt N

noncomputable def case1Eminus (N : ℝ) : ℝ := -1 - 1 / Real.sqrt N

theorem case1_gap (N : ℝ) : case1Eplus N - case1Eminus N = 2 / Real.sqrt N := by
  unfold case1Eplus case1Eminus
  ring

theorem case1_optimal_time (N : ℝ) (hN : 0 < N) :
    Real.pi / (case1Eplus N - case1Eminus N) = Real.pi * Real.sqrt N / 2 := by
  rw [case1_gap]
  have hs : Real.sqrt N ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hN)
  field_simp

noncomputable def case2HalfGap (γ C N k μ : ℝ) : ℝ :=
  γ * C * μ * Real.sqrt (N / k)

noncomputable def case2Eplus (γ C N k μ : ℝ) : ℝ :=
  -γ * k + case2HalfGap γ C N k μ

noncomputable def case2Eminus (γ C N k μ : ℝ) : ℝ :=
  -γ * k - case2HalfGap γ C N k μ

theorem case2_halfGap (γ C N k μ : ℝ) :
    (case2Eplus γ C N k μ - case2Eminus γ C N k μ) / 2 = case2HalfGap γ C N k μ := by
  unfold case2Eplus case2Eminus
  ring

noncomputable def twoLevelAmplitude (o Ep Em t : ℝ) : ℂ :=
  ((o / 2 : ℝ) : ℂ) *
    (Complex.exp (-(Em * t) * Complex.I) - Complex.exp (-(Ep * t) * Complex.I))

theorem norm_exp_sub_exp_mul_I (A B : ℝ) :
    ‖Complex.exp ((A : ℂ) * Complex.I) - Complex.exp ((B : ℂ) * Complex.I)‖
      = 2 * |Real.sin ((A - B) / 2)| := by
  have hfac :
      Complex.exp ((B : ℂ) * Complex.I) *
          (Complex.exp (((A - B : ℝ) : ℂ) * Complex.I) - 1)
        = Complex.exp ((A : ℂ) * Complex.I) - Complex.exp ((B : ℂ) * Complex.I) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    have harg :
        (B : ℂ) * Complex.I + ((A - B : ℝ) : ℂ) * Complex.I = (A : ℂ) * Complex.I := by
      rw [← add_mul]
      have hbc : (B : ℂ) + ((A - B : ℝ) : ℂ) = (A : ℂ) := by
        push_cast
        ring
      rw [hbc]
    rw [harg]
  rw [← hfac, norm_mul]
  rw [Complex.norm_exp_ofReal_mul_I B, one_mul]
  have hexp :
      Complex.exp (((A - B : ℝ) : ℂ) * Complex.I)
        = Complex.exp (Complex.I * ((A - B : ℝ) : ℂ)) :=
    congrArg Complex.exp (mul_comm _ _)
  rw [hexp, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul]
  norm_num

theorem twoLevelAmplitude_normSq (o Ep Em t : ℝ) :
    ‖twoLevelAmplitude o Ep Em t‖ ^ 2
      = o ^ 2 * Real.sin ((Ep - Em) * t / 2) ^ 2 := by
  unfold twoLevelAmplitude
  rw [norm_mul]
  have hcoef : ‖((o / 2 : ℝ) : ℂ)‖ = |o / 2| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hcoef]
  have h := norm_exp_sub_exp_mul_I (-(Em * t)) (-(Ep * t))
  have harg : (-(Em * t) - -(Ep * t)) / 2 = (Ep - Em) * t / 2 := by ring
  rw [harg] at h
  simp only [Complex.ofReal_neg, Complex.ofReal_mul] at h
  rw [h]
  simp only [mul_pow, sq_abs]
  ring

theorem case1_successProbability (N t : ℝ) (hN : 0 < N) :
    ‖twoLevelAmplitude 1 (case1Eplus N) (case1Eminus N) t‖ ^ 2
      = Real.sin (t / Real.sqrt N) ^ 2 := by
  rw [twoLevelAmplitude_normSq]
  have hs : Real.sqrt N ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hN)
  have harg : (case1Eplus N - case1Eminus N) * t / 2 = t / Real.sqrt N := by
    unfold case1Eplus case1Eminus
    field_simp
    ring
  rw [harg]
  ring

theorem case1_success_one (N : ℝ) (hN : 0 < N) :
    ‖twoLevelAmplitude 1 (case1Eplus N) (case1Eminus N)
        (Real.pi * Real.sqrt N / 2)‖ ^ 2 = 1 := by
  rw [case1_successProbability N _ hN]
  have hs : Real.sqrt N ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hN)
  have harg : (Real.pi * Real.sqrt N / 2) / Real.sqrt N = Real.pi / 2 := by
    field_simp
  rw [harg, Real.sin_pi_div_two]
  norm_num

noncomputable def case2Overlap (C N k μ : ℝ) : ℝ :=
  C * μ * N / (k * Real.sqrt k)

theorem case2_successProbability (γ C N k μ o t : ℝ) :
    ‖twoLevelAmplitude o (case2Eplus γ C N k μ) (case2Eminus γ C N k μ) t‖ ^ 2
      = o ^ 2 * Real.sin (case2HalfGap γ C N k μ * t) ^ 2 := by
  rw [twoLevelAmplitude_normSq]
  have harg : (case2Eplus γ C N k μ - case2Eminus γ C N k μ) * t / 2
      = case2HalfGap γ C N k μ * t := by
    unfold case2Eplus case2Eminus
    ring
  rw [harg]

theorem case2_overlap_halfGap_relation (C N k μ : ℝ) (hN : 0 < N) (hk : 0 < k) :
    (1 / k) * C * μ * Real.sqrt (N / k) * Real.sqrt N = case2Overlap C N k μ := by
  unfold case2Overlap
  rw [Real.sqrt_div' N hk.le]
  have hsN : Real.sqrt N ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hN)
  have hsk : Real.sqrt k ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hk)
  have hk0 : k ≠ 0 := ne_of_gt hk
  have hsqN : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN.le
  have hsqk : Real.sqrt k ^ 2 = k := Real.sq_sqrt hk.le
  have hsqNm : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN.le
  have hsqkm : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt hk.le
  field_simp
  try simp only [hsqN]
  try ring

theorem case2_success_one_under_approximation (N : ℝ) (hN : 0 < N) :
    (1 : ℝ) ^ 2 * Real.sin ((1 / Real.sqrt N) * (Real.pi * Real.sqrt N / 2)) ^ 2 = 1 := by
  have hs : Real.sqrt N ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hN)
  have harg : (1 / Real.sqrt N) * (Real.pi * Real.sqrt N / 2) = Real.pi / 2 := by
    field_simp
  rw [harg, Real.sin_pi_div_two]
  norm_num

end Qatlib.Papers.NoGlobalSym14.ScalarModels
