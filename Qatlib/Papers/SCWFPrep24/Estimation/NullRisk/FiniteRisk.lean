/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.FiniteStats.BornEstimator.FiniteLaw

set_option backward.isDefEq.respectTransparency false

/-!
# Finite Risk

Averaging actual finite outcome laws under a fixed finite input prior.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
open Qatlib.Foundations.FiniteStats.BornEstimator

/-- Averaging actual finite outcome laws under a fixed finite input prior. -/
def priorLaw {Z O : Type*} [Fintype Z] (w : Z → ℝ) (p : Z → O → ℝ) : O → ℝ :=
  fun o => ∑ z, w z * p z o

/-- The actual prior mean equals the prior average of the actual input means. -/
theorem priorLaw_mean {Z O : Type*} [Fintype Z] [Fintype O]
    (w : Z → ℝ) (p : Z → O → ℝ) (y : O → ℝ) :
    mean (priorLaw w p) y = ∑ z, w z * mean (p z) y := by
  unfold mean priorLaw
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum, mul_assoc]

/-- A genuine finite probability law has second moment at least its squared mean. -/
theorem finite_mean_sq_le_second {O : Type*} [Fintype O]
    (p : O → ℝ) (hp : ∀ o, 0 ≤ p o) (hn : ∑ o, p o = 1) (y : O → ℝ) :
    (mean p y)^2 ≤ second p y := by
  have hv : 0 ≤ variance p y := by
    exact Finset.sum_nonneg fun o _ => mul_nonneg (hp o) (sq_nonneg _)
  rw [variance_eq p hn y] at hv
  linarith

/-- Leaf domination controls the second moment of any signed finite output. This is a component lemma; the physical shared-phase priors must independently prove the leaf domination. -/
theorem second_le_of_leaf_domination {O : Type*} [Fintype O]
    (p0 p1 y : O → ℝ) (hd : ∀ o, p1 o ≤ 24 * p0 o) :
    second p1 y ≤ 24 * second p0 y := by
  unfold second mean
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun o _ => by
    have h := mul_le_mul_of_nonneg_right (hd o) (sq_nonneg (y o))
    nlinarith only [h]

/-- Some real input in a finite normalized prior attains any lower bound on its average score. -/
theorem exists_score_ge_prior_mean {Z : Type*} [Fintype Z]
    (w f : Z → ℝ) (hw : ∀ z, 0 ≤ w z) (hn : ∑ z, w z = 1)
    (a : ℝ) (ha : a ≤ ∑ z, w z * f z) :
    ∃ z, a ≤ f z := by
  by_contra h
  push Not at h
  have hz : ∃ z, 0 < w z := by
    by_contra hc
    push Not at hc
    have he : ∑ z, w z = 0 := Finset.sum_eq_zero fun z _ => le_antisymm (hc z) (hw z)
    linarith
  obtain ⟨z, hz⟩ := hz
  have hs : (∑ z, w z * f z) < ∑ z, w z * a := by
    exact Finset.sum_lt_sum (fun z _ => mul_le_mul_of_nonneg_left (h z).le (hw z))
      ⟨z, Finset.mem_univ z, mul_lt_mul_of_pos_left (h z) hz⟩
  rw [← Finset.sum_mul, hn, one_mul] at hs
  linarith

/-- Actual finite prior laws remain normalized when every input law is normalized. -/
theorem priorLaw_sum_one {Z O : Type*} [Fintype Z] [Fintype O]
    (w : Z → ℝ) (p : Z → O → ℝ) (hw : ∑ z, w z = 1)
    (hp : ∀ z, ∑ o, p z o = 1) : ∑ o, priorLaw w p o = 1 := by
  unfold priorLaw
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hp, mul_one]
  exact hw

/-- A uniform bounded-bias estimator has a genuinely attained null variance floor once the actual finite physical priors establish leaf domination. The strict beta < S condition is retained before squaring. -/
theorem bounded_bias_null_variance_from_priors
    {Z0 Z1 O : Type*} [Fintype Z0] [Fintype Z1] [Fintype O]
    (w0 : Z0 → ℝ) (w1 : Z1 → ℝ) (p0 : Z0 → O → ℝ) (p1 : Z1 → O → ℝ)
    (y : O → ℝ) (loss1 : Z1 → ℝ) (S beta : ℝ)
    (hw0 : ∀ z, 0 ≤ w0 z) (hw1 : ∀ z, 0 ≤ w1 z)
    (hnw0 : ∑ z, w0 z = 1) (hnw1 : ∑ z, w1 z = 1)
    (hnp0 : ∀ z, ∑ o, p0 z o = 1) (hnp1 : ∀ z, ∑ o, p1 z o = 1)
    (hp1 : ∀ z o, 0 ≤ p1 z o) (hbeta : 0 ≤ beta) (hsmall : beta < S)
    (hnull : ∀ z, |mean (p0 z) y| ≤ beta)
    (halt : ∀ z, |mean (p1 z) y - loss1 z| ≤ beta)
    (hgap : ∀ z, S ≤ loss1 z)
    (hdom : ∀ o, priorLaw w1 p1 o ≤ 24 * priorLaw w0 p0 o) :
    ∃ z, (S - beta)^2 / 24 - beta^2 ≤ variance (p0 z) y := by
  have hmean : S - beta ≤ mean (priorLaw w1 p1) y := by
    rw [priorLaw_mean]
    calc S - beta = ∑ z, w1 z * (S - beta) := by
           rw [← Finset.sum_mul, hnw1, one_mul]
         _ ≤ ∑ z, w1 z * mean (p1 z) y := by
           apply Finset.sum_le_sum
           intro z _
           apply mul_le_mul_of_nonneg_left _ (hw1 z)
           have hb := (abs_le.mp (halt z)).1
           linarith [hgap z]
  have hnonneg : ∀ o, 0 ≤ priorLaw w1 p1 o := by
    intro o
    exact Finset.sum_nonneg fun z _ => mul_nonneg (hw1 z) (hp1 z o)
  have hsquare : (S - beta)^2 ≤ second (priorLaw w1 p1) y := by
    calc (S - beta)^2 ≤ (mean (priorLaw w1 p1) y)^2 :=
           pow_le_pow_left₀ (sub_pos.mpr hsmall).le hmean 2
         _ ≤ second (priorLaw w1 p1) y :=
           finite_mean_sq_le_second _ hnonneg (priorLaw_sum_one w1 p1 hnw1 hnp1) y
  have hd := second_le_of_leaf_domination (priorLaw w0 p0) (priorLaw w1 p1) y hdom
  have hbeta_sq : 0 ≤ beta^2 := by simpa only [pow_two] using mul_nonneg hbeta hbeta
  have hmeansquare (z : Z0) : (mean (p0 z) y)^2 ≤ beta^2 := by
    have habs := pow_le_pow_left₀ (abs_nonneg (mean (p0 z) y)) (hnull z) 2
    simpa only [sq_abs] using habs
  have hvariance : second (priorLaw w0 p0) y - beta^2 ≤
      ∑ z, w0 z * variance (p0 z) y := by
    have he : second (priorLaw w0 p0) y = ∑ z, w0 z * second (p0 z) y :=
      priorLaw_mean w0 p0 (fun o => y o^2)
    rw [he]
    calc (∑ z, w0 z * second (p0 z) y) - beta^2 =
          ∑ z, w0 z * (second (p0 z) y - beta^2) := by
            simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hnw0, one_mul]
         _ ≤ ∑ z, w0 z * variance (p0 z) y := by
            apply Finset.sum_le_sum
            intro z _
            apply mul_le_mul_of_nonneg_left _ (hw0 z)
            rw [variance_eq _ (hnp0 z)]
            linarith [hmeansquare z, hbeta_sq]
  apply exists_score_ge_prior_mean w0 (fun z => variance (p0 z) y) hw0 hnw0
  linarith

end Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
