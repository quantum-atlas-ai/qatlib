/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.ReadoutTools.PureStateEventLipschitzStat

/-!
# Lipschitz continuity of pure-state events

This module proves that the probability of a computational-basis event changes by at most the
Euclidean distance between normalized pure states. The result is a finite-dimensional
measurement stability estimate in the setting of [Watrous2018].

## Main statements

* `pureStateEventLipschitz`: every event probability is Lipschitz with constant one on
  normalized state vectors.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

set_option autoImplicit false
namespace Qatlib.Concepts.GradientOracle.ReadoutTools
open Qatlib
open scoped Classical
set_option warningAsError false

/-- The difference of squared complex norms equals the real part of the conjugate difference
multiplied by the sum. -/
private theorem re_star_sub_mul_add (a b : ℂ) :
    ‖a‖^2 - ‖b‖^2 = Complex.re (starRingEnd ℂ (a - b) * (a + b)) := by
  have h1 : starRingEnd ℂ (a - b) * (a + b)
      = starRingEnd ℂ a * a - starRingEnd ℂ b * b
        + (starRingEnd ℂ a * b - starRingEnd ℂ b * a) := by
    rw [map_sub]
    ring
  have h2 : Complex.re (starRingEnd ℂ a * b - starRingEnd ℂ b * a) = 0 := by
    rw [Complex.sub_re, Complex.mul_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.conj_re, Complex.conj_im]
    ring
  have h3 (c : ℂ) : Complex.re (starRingEnd ℂ c * c) = ‖c‖^2 := by
    rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply]
    ring
  rw [h1, Complex.add_re, Complex.sub_re, h3, h3, h2]
  ring

/-- For normalized finite pure states, every computational-basis event-probability difference is
bounded by the Euclidean norm of the state difference. See [Watrous2018]. -/
theorem pureStateEventLipschitz : PureStateEventLipschitz := by
  intro I _ _ u v hu hv E
  have hu' : ∑ i, ‖u i‖^2 = 1 := hu
  have hv' : ∑ i, ‖v i‖^2 = 1 := hv
  have hnu : ‖toEuclidean_fromVec u‖ = 1 := (normalized_iff_norm_toEuclidean_fromVec u).mp hu
  have hnv : ‖toEuclidean_fromVec v‖ = 1 := (normalized_iff_norm_toEuclidean_fromVec v).mp hv
  set t : QState I := fun i => if i ∈ E then (u + v) i else -((u + v) i) with ht_def
  set a : I → ℝ := fun i => Complex.re (starRingEnd ℂ ((u - v) i) * ((u + v) i)) with ha_def
  have hkey : ∀ i : I, a i = ‖u i‖^2 - ‖v i‖^2 := by
    intro i
    simpa only [ha_def, Pi.sub_apply, Pi.add_apply] using! (re_star_sub_mul_add (u i) (v i)).symm
  have hzero : ∑ i ∈ Finset.univ.filter (fun i => i ∈ E), a i
      + ∑ i ∈ Finset.univ.filter (fun i => ¬ i ∈ E), a i = 0 := by
    rw [Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => i ∈ E) a,
      Finset.sum_congr rfl (fun i _ => hkey i), Finset.sum_sub_distrib, hu', hv', sub_self]
  have hEfilter : Finset.univ.filter (fun i => i ∈ E) = E := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hA : ∑ i ∈ Finset.univ.filter (fun i => i ∈ E), a i
      = MeasureProb u E - MeasureProb v E := by
    rw [hEfilter]
    simp only [MeasureProb, BornProb, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => hkey i
  have hB : ∑ i ∈ Finset.univ.filter (fun i => ¬ i ∈ E), a i
      = -(MeasureProb u E - MeasureProb v E) := by
    have := hzero
    rw [hA] at this
    linarith
  have hinner_sum (x y : QState I) :
      Complex.re (inner ℂ (toEuclidean_fromVec x) (toEuclidean_fromVec y))
        = ∑ i : I, Complex.re (starRingEnd ℂ (x i) * y i) := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, Complex.re_sum, toEuclidean_fromVec_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]
  have hpt : ∀ i : I, Complex.re (starRingEnd ℂ ((u - v) i) * t i)
      = if i ∈ E then a i else -(a i) := by
    intro i
    by_cases h : i ∈ E
    · simp only [ht_def, if_pos h, ha_def]
    · simp only [ht_def, if_neg h, ha_def, mul_neg, Complex.neg_re]
  have hinner : Complex.re (inner ℂ (toEuclidean_fromVec (u - v)) (toEuclidean_fromVec t))
      = 2 * (MeasureProb u E - MeasureProb v E) := by
    rw [hinner_sum, Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_ite,
      Finset.sum_neg_distrib, hA, hB]
    ring
  have hcs := norm_inner_le_norm (𝕜 := ℂ) (toEuclidean_fromVec (u - v)) (toEuclidean_fromVec t)
  have hre : |MeasureProb u E - MeasureProb v E|
      ≤ 2⁻¹ * (‖toEuclidean_fromVec (u - v)‖ * ‖toEuclidean_fromVec t‖) := by
    have h1 : |2 * (MeasureProb u E - MeasureProb v E)|
        ≤ ‖toEuclidean_fromVec (u - v)‖ * ‖toEuclidean_fromVec t‖ := by
      rw [← hinner]
      calc |Complex.re (inner ℂ (toEuclidean_fromVec (u - v)) (toEuclidean_fromVec t))|
          ≤ ‖inner ℂ (toEuclidean_fromVec (u - v)) (toEuclidean_fromVec t)‖ :=
            Complex.abs_re_le_norm _
        _ ≤ ‖toEuclidean_fromVec (u - v)‖ * ‖toEuclidean_fromVec t‖ := hcs
    have h2 : (2 : ℝ) * |MeasureProb u E - MeasureProb v E|
        = |2 * (MeasureProb u E - MeasureProb v E)| := by
      rw [abs_mul, abs_two]
    rw [← h2] at h1
    calc |MeasureProb u E - MeasureProb v E|
        = 2⁻¹ * ((2 : ℝ) * |MeasureProb u E - MeasureProb v E|) := by
          field_simp
      _ ≤ 2⁻¹ * (‖toEuclidean_fromVec (u - v)‖ * ‖toEuclidean_fromVec t‖) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
  have hnormt : ‖toEuclidean_fromVec t‖ = ‖toEuclidean_fromVec (u + v)‖ := by
    have hsq : ‖toEuclidean_fromVec t‖^2 = ‖toEuclidean_fromVec (u + v)‖^2 := by
      rw [norm_toEuclidean_fromVec_sq, norm_toEuclidean_fromVec_sq]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : i ∈ E
      · simp only [ht_def, if_pos h]
      · simp only [ht_def, if_neg h, norm_neg]
    calc ‖toEuclidean_fromVec t‖ = Real.sqrt (‖toEuclidean_fromVec t‖^2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt (‖toEuclidean_fromVec (u + v)‖^2) := by rw [hsq]
      _ = ‖toEuclidean_fromVec (u + v)‖ := Real.sqrt_sq (norm_nonneg _)
  have hadd : toEuclidean_fromVec (u + v) = toEuclidean_fromVec u + toEuclidean_fromVec v := by
    simp only [toEuclidean_fromVec, WithLp.toLp_add]
  have hs2 : ‖toEuclidean_fromVec (u + v)‖ ≤ 2 := by
    rw [hadd]
    calc ‖toEuclidean_fromVec u + toEuclidean_fromVec v‖
        ≤ ‖toEuclidean_fromVec u‖ + ‖toEuclidean_fromVec v‖ := norm_add_le _ _
      _ = 2 := by rw [hnu, hnv]; ring
  calc |MeasureProb u E - MeasureProb v E|
      ≤ 2⁻¹ * (‖toEuclidean_fromVec (u - v)‖ * ‖toEuclidean_fromVec t‖) := hre
    _ = 2⁻¹ * (‖toEuclidean_fromVec (u - v)‖ * ‖toEuclidean_fromVec (u + v)‖) := by
          rw [hnormt]
    _ ≤ 2⁻¹ * ‖toEuclidean_fromVec (u - v)‖ * 2 := by
          have hW : 0 ≤ ‖toEuclidean_fromVec (u - v)‖ := norm_nonneg _
          have hc : 0 ≤ 2⁻¹ * ‖toEuclidean_fromVec (u - v)‖ := by positivity
          have hle := mul_le_mul_of_nonneg_left hs2 hc
          nlinarith [hle, hW]
    _ = ‖toEuclidean_fromVec (u - v)‖ := by
          ring

end Qatlib.Concepts.GradientOracle.ReadoutTools
