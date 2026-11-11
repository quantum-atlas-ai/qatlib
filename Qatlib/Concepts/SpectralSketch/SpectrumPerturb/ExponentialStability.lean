/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Norm
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Exponential stability from spectral negativity

This module proves exponential decay of the exponential of an element of a complex Banach
algebra whose spectrum lies in the open left half-plane. The argument uses geometric bounds on
powers and a sufficiently small Euler step, in the spectral framework of [ReedSimon1980I].

## Main statements

* `geometric_norm_powers`: bounds powers when the spectral radius is less than one.
* `exists_small_euler_step`: places a positive Euler step inside the spectral unit disk.
* `exponential_stability_of_negative_spectrum`: obtains a uniform exponential decay bound for
  nonnegative times.

## References

* [Reed and Simon, 1980][ReedSimon1980I]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Filter NormedSpace
open scoped Topology NNReal ENNReal

set_option autoImplicit false
namespace Qatlib.Concepts.SpectralSketch.SpectrumPerturb

variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B]
  [CompleteSpace B] [NormOneClass B] [Nontrivial B]

omit [Nontrivial B] in

/-- If the spectral radius of `b` is less than one, its powers satisfy `‖b ^ n‖ ≤ C * q ^ n` for
some `0 < q < 1` and `1 ≤ C`. -/
theorem geometric_norm_powers (b : B)
    (hb : spectralRadius ℂ b < 1) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ n : ℕ, ‖b ^ n‖ ≤ C * q ^ n := by
  obtain ⟨q, hradq, hq1⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hb
  have hq0e : (0 : ℝ≥0∞) < q := lt_of_le_of_lt bot_le hradq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq0e
  have hq1r : (q : ℝ) < 1 := by exact_mod_cast hq1
  have hevent :=
    (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius b).eventually
      (gt_mem_nhds hradq)
  have heventpow : ∀ᶠ n : ℕ in atTop, |‖b ^ n‖| ≤ (q : ℝ) ^ n := by
    filter_upwards [hevent, eventually_gt_atTop (0 : ℕ)] with n hn hn0
    have hroot : ‖b ^ n‖ ^ (1 / (n : ℝ)) < (q : ℝ) :=
      (ENNReal.ofReal_lt_coe_iff
        (Real.rpow_nonneg (norm_nonneg (b ^ n)) _)).mp hn
    have hp := pow_le_pow_left₀
      (Real.rpow_nonneg (norm_nonneg (b ^ n)) (1 / (n : ℝ))) hroot.le n
    simpa only [one_div,
      Real.rpow_inv_natCast_pow (norm_nonneg (b ^ n)) (Nat.ne_of_gt hn0),
      abs_of_nonneg (norm_nonneg (b ^ n))] using hp
  have hinput : ∃ q' ∈ Set.Ioo (0 : ℝ) 1,
      ∀ᶠ n : ℕ in atTop, |‖b ^ n‖| ≤ q' ^ n :=
    ⟨(q : ℝ), ⟨hq0, hq1r⟩, heventpow⟩
  have hout : ∃ q' ∈ Set.Ioo (0 : ℝ) 1, ∃ C > 0,
      ∀ n : ℕ, |‖b ^ n‖| ≤ C * q' ^ n :=
    ((TFAE_exists_lt_isLittleO_pow (fun n : ℕ => ‖b ^ n‖) 1).out 8 6).mp
      hinput
  obtain ⟨q', hq', C, hC0, hC⟩ := hout
  refine ⟨q', hq'.1, hq'.2, C, ?_, ?_⟩
  · simpa using hC 0
  · intro n
    simpa only [abs_of_nonneg (norm_nonneg (b ^ n))] using hC n

/-- If every spectral value of `a` has negative real part, some positive Euler step `1 + (h : ℂ)
• a` has spectral radius less than one. -/
theorem exists_small_euler_step (a : B)
    (hneg : ∀ z ∈ spectrum ℂ a, z.re < 0) :
    ∃ h : ℝ, 0 < h ∧ spectralRadius ℂ (1 + (h : ℂ) • a) < 1 := by
  obtain ⟨z₀, hz₀, hmax⟩ := (spectrum.isCompact a).exists_isMaxOn
    (spectrum.nonempty a) Complex.continuous_re.continuousOn
  let δ : ℝ := -z₀.re
  have hδ : 0 < δ := neg_pos.mpr (hneg z₀ hz₀)
  let h : ℝ := δ / (‖a‖ ^ 2 + 1)
  have hden : 0 < ‖a‖ ^ 2 + 1 := by positivity
  have hh : 0 < h := div_pos hδ hden
  have hhden : h * (‖a‖ ^ 2 + 1) = δ :=
    div_mul_cancel₀ _ hden.ne'
  have hsmall : h * ‖a‖ ^ 2 < δ := by nlinarith
  refine ⟨h, hh, ?_⟩
  have hmap : spectrum ℂ (1 + (h : ℂ) • a) =
      (fun z : ℂ => 1 + (h : ℂ) * z) '' spectrum ℂ a := by
    have hm := spectrum.map_polynomial_aeval a
      (Polynomial.C 1 + Polynomial.C (h : ℂ) * Polynomial.X)
    simp only [Polynomial.aeval_add, Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_X,
      Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_one,
      map_one] at hm
    simpa only [Algebra.smul_def] using hm
  apply spectrum.spectralRadius_lt_of_forall_lt
  intro w hw
  rw [hmap] at hw
  obtain ⟨z, hz, rfl⟩ := hw
  have hre : z.re ≤ -δ := by simpa [δ] using hmax hz
  have hn : ‖z‖ ≤ ‖a‖ := spectrum.norm_le_norm_of_mem hz
  have hnsq : ‖z‖ ^ 2 ≤ ‖a‖ ^ 2 := by
    nlinarith [norm_nonneg z, norm_nonneg a]
  have hformula : ‖1 + (h : ℂ) * z‖ ^ 2 =
      1 + 2 * h * z.re + h ^ 2 * ‖z‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re,
      Complex.add_im, Complex.one_re, Complex.one_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hre' : 2 * h * z.re ≤ 2 * h * (-δ) := by
    exact mul_le_mul_of_nonneg_left hre (by positivity)
  have hnsq' : h ^ 2 * ‖z‖ ^ 2 ≤ h ^ 2 * ‖a‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hnsq (sq_nonneg h)
  have hs' : h * (h * ‖a‖ ^ 2) < h * δ :=
    mul_lt_mul_of_pos_left hsmall hh
  have hnorm : ‖1 + (h : ℂ) * z‖ < 1 := by
    nlinarith [norm_nonneg (1 + (h : ℂ) * z), mul_pos hh hδ]
  exact_mod_cast hnorm

omit [NormOneClass B] [Nontrivial B] in

/-- A geometric bound `‖b ^ n‖ ≤ C * q ^ n` implies `‖exp ((s : ℂ) • b)‖ ≤ C * Real.exp (q * s)`
for nonnegative `s`. -/
theorem norm_exp_smul_le_of_geometric (b : B) (q C : ℝ)
    (hp : ∀ n : ℕ, ‖b ^ n‖ ≤ C * q ^ n)
    (s : ℝ) (hs : 0 ≤ s) :
    ‖exp ((s : ℂ) • b)‖ ≤ C * Real.exp (q * s) := by
  have he := exp_series_hasSum_exp' (𝕂 := ℂ) ((s : ℂ) • b)
  have hr : HasSum (fun n : ℕ => C * ((n.factorial : ℝ)⁻¹ * (q * s) ^ n))
      (C * Real.exp (q * s)) := by
    simpa only [smul_eq_mul, ← Real.exp_eq_exp_ℝ] using
      HasSum.mul_left C (exp_series_hasSum_exp' (𝕂 := ℝ) (q * s))
  apply he.norm_le_of_bounded hr
  intro n
  calc
    ‖((n.factorial : ℂ)⁻¹) • (((s : ℂ) • b) ^ n)‖
        = (n.factorial : ℝ)⁻¹ * (s ^ n * ‖b ^ n‖) := by
          rw [norm_smul, smul_pow, norm_smul, norm_inv, Complex.norm_natCast,
            norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
    _ ≤ (n.factorial : ℝ)⁻¹ * (s ^ n * (C * q ^ n)) := by
      gcongr
      exact hp n
    _ = C * ((n.factorial : ℝ)⁻¹ * (q * s) ^ n) := by
      rw [mul_pow]
      ring

/-- If the spectrum of `a` lies in the open left half-plane, there exist `1 ≤ C` and `0 < μ`
such that `‖exp ((t : ℂ) • a)‖ ≤ C * Real.exp (-μ * t)` for all nonnegative `t`. -/
theorem exponential_stability_of_negative_spectrum (a : B)
    (hneg : ∀ z ∈ spectrum ℂ a, z.re < 0) :
    ∃ C μ : ℝ, 1 ≤ C ∧ 0 < μ ∧
      ∀ t : ℝ, 0 ≤ t → ‖exp ((t : ℂ) • a)‖ ≤ C * Real.exp (-μ * t) := by
  letI : NormedAlgebra ℚ B := .restrictScalars ℚ ℂ B
  obtain ⟨h, hh, hrad⟩ := exists_small_euler_step a hneg
  let b : B := 1 + (h : ℂ) • a
  obtain ⟨q, hq0, hq1, C, hC, hp⟩ := geometric_norm_powers b hrad
  refine ⟨C, (1 - q) / h, hC, div_pos (sub_pos.mpr hq1) hh, ?_⟩
  intro t ht
  let s : ℝ := t / h
  have hs : 0 ≤ s := div_nonneg ht hh.le
  have hsh : (s : ℂ) * (h : ℂ) = (t : ℂ) := by
    norm_cast
    exact div_mul_cancel₀ t hh.ne'
  have hdecomp : (t : ℂ) • a =
      algebraMap ℂ B (-(s : ℂ)) + (s : ℂ) • b := by
    dsimp only [b]
    rw [Algebra.algebraMap_eq_smul_one, smul_add, smul_smul, hsh]
    simp only [← add_assoc, ← add_smul, neg_add_cancel, zero_smul, zero_add]
  have hfactor : exp ((t : ℂ) • a) =
      algebraMap ℂ B (exp (-(s : ℂ))) * exp ((s : ℂ) • b) := by
    rw [hdecomp, exp_add_of_commute (Algebra.commutes (-(s : ℂ)) ((s : ℂ) • b)),
      ← algebraMap_exp_comm]
  have hscalar : ‖algebraMap ℂ B (exp (-(s : ℂ)))‖ = Real.exp (-s) := by
    rw [norm_algebraMap', ← Complex.exp_eq_exp_ℂ, Complex.norm_exp]
    simp
  calc
    ‖exp ((t : ℂ) • a)‖
        ≤ ‖algebraMap ℂ B (exp (-(s : ℂ)))‖ * ‖exp ((s : ℂ) • b)‖ := by
          rw [hfactor]
          exact norm_mul_le _ _
    _ ≤ Real.exp (-s) * (C * Real.exp (q * s)) := by
      rw [hscalar]
      gcongr
      exact norm_exp_smul_le_of_geometric b q C hp s hs
    _ = C * Real.exp (-((1 - q) / h) * t) := by
      rw [← mul_assoc, mul_comm (Real.exp (-s)) C, mul_assoc, ← Real.exp_add]
      congr 1
      dsimp only [s]
      congr 1
      ring

end Qatlib.Concepts.SpectralSketch.SpectrumPerturb
