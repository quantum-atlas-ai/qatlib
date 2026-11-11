/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# Scalar two-level perturbation models

Defines the critical rates `gammaC1` and `gammaC2` and explicit two-level energies for search on
strongly regular graphs. The results compute gaps and squared amplitudes within these scalar
models, including unit success at the specified case-one transfer time. See
[JanmarkMeyerWong2014] for the surrounding analysis.

## Main statements

* `case1_gap`: The gap between the two case-one model energies is `2 / Real.sqrt N`.
* `twoLevelAmplitude_normSq`: The squared norm of `twoLevelAmplitude` is the squared overlap
  times the squared sine of half the energy gap multiplied by time.
* `case1_success_one`: For positive `N`, the case-one model has unit success probability at time
  `Real.pi * Real.sqrt N / 2`.

## References

* [Janmark et al., 2014][JanmarkMeyerWong2014]
-/

set_option autoImplicit false

namespace Qatlib.Papers.NoGlobalSym14.ScalarModels

/-- The case-one critical rate `1 / k`. -/
noncomputable def gammaC1 (k : ℝ) : ℝ := 1 / k

/-- The corrected case-two critical rate `1 / k + 1 / ((N - 1) * μ)`. -/
noncomputable def gammaC2 (k N μ : ℝ) : ℝ := 1 / k + 1 / ((N - 1) * μ)

/-- For nonzero `k`, the case-one critical rate makes the leading energy `-γ * k` equal to `-1`
[JanmarkMeyerWong2014]. -/
theorem case1_critical_gamma_degenerate (k : ℝ) (hk : k ≠ 0) :
    -(gammaC1 k) * k = -1 := by
  unfold gammaC1
  field_simp

/-- The case-two critical rate exceeds `1 / k` by exactly `1 / ((N - 1) * μ)`
[JanmarkMeyerWong2014]. -/
theorem case2_critical_gamma_excess (k N μ : ℝ) :
    gammaC2 k N μ - 1 / k = 1 / ((N - 1) * μ) := by
  unfold gammaC2
  rw [add_sub_cancel_left]

/-- The upper case-one model energy `-1 + 1 / Real.sqrt N`. -/
noncomputable def case1Eplus (N : ℝ) : ℝ := -1 + 1 / Real.sqrt N

/-- The lower case-one model energy `-1 - 1 / Real.sqrt N`. -/
noncomputable def case1Eminus (N : ℝ) : ℝ := -1 - 1 / Real.sqrt N

/-- The gap between the two case-one model energies is `2 / Real.sqrt N` [JanmarkMeyerWong2014]. -/
theorem case1_gap (N : ℝ) : case1Eplus N - case1Eminus N = 2 / Real.sqrt N := by
  unfold case1Eplus case1Eminus
  ring

/-- For positive `N`, π divided by the case-one energy gap is `Real.pi * Real.sqrt N / 2`. -/
theorem case1_optimal_time (N : ℝ) (hN : 0 < N) :
    Real.pi / (case1Eplus N - case1Eminus N) = Real.pi * Real.sqrt N / 2 := by
  rw [case1_gap]
  have hs : Real.sqrt N ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hN)
  field_simp

/-- The case-two model half-gap `γ * C * μ * Real.sqrt (N / k)`. -/
noncomputable def case2HalfGap (γ C N k μ : ℝ) : ℝ :=
  γ * C * μ * Real.sqrt (N / k)

/-- The upper case-two model energy, obtained by adding `case2HalfGap` to `-γ * k`. -/
noncomputable def case2Eplus (γ C N k μ : ℝ) : ℝ :=
  -γ * k + case2HalfGap γ C N k μ

/-- The lower case-two model energy, obtained by subtracting `case2HalfGap` from `-γ * k`. -/
noncomputable def case2Eminus (γ C N k μ : ℝ) : ℝ :=
  -γ * k - case2HalfGap γ C N k μ

/-- Half the difference between the case-two model energies equals `case2HalfGap`. -/
theorem case2_halfGap (γ C N k μ : ℝ) :
    (case2Eplus γ C N k μ - case2Eminus γ C N k μ) / 2 = case2HalfGap γ C N k μ := by
  unfold case2Eplus case2Eminus
  ring

/-- The two-level amplitude `(o / 2) * (exp(-i Em t) - exp(-i Ep t))` for real overlap and
energies. -/
noncomputable def twoLevelAmplitude (o Ep Em t : ℝ) : ℂ :=
  ((o / 2 : ℝ) : ℂ) *
    (Complex.exp (-(Em * t) * Complex.I) - Complex.exp (-(Ep * t) * Complex.I))

/-- The distance between two unit complex exponentials is twice the absolute sine of half their
phase difference. -/
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

/-- The squared norm of `twoLevelAmplitude` is the squared overlap times the squared sine of
half the energy gap multiplied by time. -/
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

/-- For positive `N`, the unit-overlap case-one model has success probability `sin(t / √N)²`. -/
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

/-- For positive `N`, the case-one model has unit success probability at time `Real.pi *
Real.sqrt N / 2` [JanmarkMeyerWong2014]. -/
theorem case1_success_one (N : ℝ) (hN : 0 < N) :
    ‖twoLevelAmplitude 1 (case1Eplus N) (case1Eminus N)
        (Real.pi * Real.sqrt N / 2)‖ ^ 2 = 1 := by
  rw [case1_successProbability N _ hN]
  have hs : Real.sqrt N ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hN)
  have harg : (Real.pi * Real.sqrt N / 2) / Real.sqrt N = Real.pi / 2 := by
    field_simp
  rw [harg, Real.sin_pi_div_two]
  norm_num

/-- The case-two model overlap `C * μ * N / (k * Real.sqrt k)`. -/
noncomputable def case2Overlap (C N k μ : ℝ) : ℝ :=
  C * μ * N / (k * Real.sqrt k)

/-- The case-two model has squared amplitude `o² * sin(case2HalfGap γ C N k μ * t)²`
[JanmarkMeyerWong2014]. -/
theorem case2_successProbability (γ C N k μ o t : ℝ) :
    ‖twoLevelAmplitude o (case2Eplus γ C N k μ) (case2Eminus γ C N k μ) t‖ ^ 2
      = o ^ 2 * Real.sin (case2HalfGap γ C N k μ * t) ^ 2 := by
  rw [twoLevelAmplitude_normSq]
  have harg : (case2Eplus γ C N k μ - case2Eminus γ C N k μ) * t / 2
      = case2HalfGap γ C N k μ * t := by
    unfold case2Eplus case2Eminus
    ring
  rw [harg]

/-- For positive `N` and `k`, the case-two half-gap expression at rate `1 / k`, multiplied by
`√N`, equals `case2Overlap`. -/
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

/-- For positive `N`, substituting unit overlap, half-gap `1 / √N`, and time `π√N / 2` into the
scalar sine law gives one. -/
theorem case2_success_one_under_approximation (N : ℝ) (hN : 0 < N) :
    (1 : ℝ) ^ 2 * Real.sin ((1 / Real.sqrt N) * (Real.pi * Real.sqrt N / 2)) ^ 2 = 1 := by
  have hs : Real.sqrt N ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hN)
  have harg : (1 / Real.sqrt N) * (Real.pi * Real.sqrt N / 2) = Real.pi / 2 := by
    field_simp
  rw [harg, Real.sin_pi_div_two]
  norm_num

end Qatlib.Papers.NoGlobalSym14.ScalarModels
