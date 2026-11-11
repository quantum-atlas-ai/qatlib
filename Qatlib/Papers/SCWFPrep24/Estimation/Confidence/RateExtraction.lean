/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.FiniteStats.BornEstimator.ConfidenceLog
import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.WeakPair
import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.PhysicalScales

set_option backward.isDefEq.respectTransparency false

/-!
# Rate Extraction

Original natural copy budgets keep the actual collision count polynomial nonnegative, including zero and one.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix ComplexOrder MatrixOrder

namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.RateExtraction
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence
open Qatlib.Foundations.FiniteStats.BornEstimator.ConfidenceLog

/-- Original natural copy budgets keep the actual collision count polynomial nonnegative, including zero and one. -/
theorem copy_polynomial_nonneg (Q : ℕ) : 0≤(Q : ℝ)*((Q : ℝ)-1) := by
  by_cases h : Q=0
  · subst Q
    norm_num
  · have hq : (1 : ℝ)≤Q := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr h)
    exact mul_nonneg (Nat.cast_nonneg Q) (by linarith)

/-- The true whole-input testing bound yields the original two collision information scales uniformly over the full original confidence interval. -/
theorem collision_information_scales (N Q : ℕ) (M δ : ℝ) (hN : 256≤N) (hM : 0<M)
    (hδ : 0<δ) (hmax : δ≤1/10)
    (hinfo : Real.exp (-(216/7 : ℝ)*(128/((N : ℝ)^2))*
      min (Q : ℝ) ((Q : ℝ)*((Q : ℝ)-1)/M))≤8*δ) :
    (N : ℝ)^2*Real.log (1/δ)≤65536*(Q : ℝ) ∧
    (N : ℝ)^2*M*Real.log (1/δ)≤65536*(Q : ℝ)^2 := by
  have hn : (N : ℝ)≠0 := by
    have h : (256 : ℝ)≤N := by exact_mod_cast hN
    linarith
  let s : ℝ := min (Q : ℝ) ((Q : ℝ)*((Q : ℝ)-1)/M)
  have hs : 0≤ s := le_min (Nat.cast_nonneg Q) (div_nonneg (copy_polynomial_nonneg Q) hM.le)
  have hl := Real.log_le_log (Real.exp_pos _) hinfo
  rw [Real.log_exp] at hl
  have hu := uniform_confidence_log δ hδ hmax
  have hi : Real.log (1/(8*δ))=-Real.log (8*δ) := by rw [one_div,Real.log_inv]
  rw [hi] at hu
  have hL : Real.log (1/δ)≤16*((216/7 : ℝ)*(128/((N : ℝ)^2)))*s := by
    change (-(216/7 : ℝ)*(128/((N : ℝ)^2)))*s≤Real.log (8*δ) at hl
    rw [show (-(216/7 : ℝ)*(128/((N : ℝ)^2)))=-((216/7 : ℝ)*(128/((N : ℝ)^2))) by ring] at hl
    linarith
  have hnL := mul_le_mul_of_nonneg_left hL (sq_nonneg (N : ℝ))
  have he : (N : ℝ)^2*(16*((216/7 : ℝ)*(128/((N : ℝ)^2)))*s)=(442368/7 : ℝ)*s := by
    field_simp [hn]
    ring
  rw [he] at hnL
  have hmid : (N : ℝ)^2*Real.log (1/δ)≤65536*s :=
    hnL.trans (mul_le_mul_of_nonneg_right (by norm_num : (442368/7 : ℝ)≤65536) hs)
  have hlin := hmid.trans (mul_le_mul_of_nonneg_left (min_le_left (Q : ℝ) ((Q : ℝ)*((Q : ℝ)-1)/M)) (by norm_num : (0 : ℝ)≤65536))
  have hfrac := hmid.trans (mul_le_mul_of_nonneg_left (min_le_right (Q : ℝ) ((Q : ℝ)*((Q : ℝ)-1)/M)) (by norm_num : (0 : ℝ)≤65536))
  have hmul := mul_le_mul_of_nonneg_right hfrac hM.le
  have hc : (65536*((Q : ℝ)*((Q : ℝ)-1)/M))*M=65536*(Q : ℝ)*((Q : ℝ)-1) := by
    field_simp [ne_of_gt hM]
  rw [hc] at hmul
  refine ⟨hlin,?_⟩
  calc
    _ = ((N : ℝ)^2*Real.log (1/δ))*M := by ring
    _ ≤ 65536*(Q : ℝ)*((Q : ℝ)-1) := hmul
    _ ≤ _ := by nlinarith [(show (0 : ℝ)≤(Q : ℝ) from Nat.cast_nonneg Q)]

/-- The actual collision information scales imply the original sum rate with one explicit confidence-uniform constant. -/
theorem collision_sum_rate (N Q : ℕ) (M δ : ℝ) (hN : 256≤N) (hM : 0<M)
    (hδ : 0<δ) (hmax : δ≤1/10)
    (hinfo : Real.exp (-(216/7 : ℝ)*(128/((N : ℝ)^2))*
      min (Q : ℝ) ((Q : ℝ)*((Q : ℝ)-1)/M))≤8*δ) :
    (N : ℝ)^2*Real.log (1/δ)+(N : ℝ)*Real.sqrt (M*Real.log (1/δ))≤131072*(Q : ℝ) := by
  have hc := collision_information_scales N Q M δ hN hM hδ hmax hinfo
  have hL : 0≤Real.log (1/δ) := Real.log_nonneg ((le_div_iff₀ hδ).2 (by linarith))
  have hs : ((N : ℝ)*Real.sqrt (M*Real.log (1/δ)))^2=(N : ℝ)^2*M*Real.log (1/δ) := by
    rw [mul_pow,Real.sq_sqrt (mul_nonneg hM.le hL)]
    ring
  have hq : 0≤(256 : ℝ)*(Q : ℝ) := by positivity
  have hroot : 0≤(N : ℝ)*Real.sqrt (M*Real.log (1/δ)) := by positivity
  have hsq : ((N : ℝ)*Real.sqrt (M*Real.log (1/δ)))^2≤(256*(Q : ℝ))^2 := by
    rw [hs]
    nlinarith [hc.2]
  have hrt := (sq_le_sq₀ hroot hq).mp hsq
  nlinarith [hc.1,(show (0 : ℝ)≤(Q : ℝ) from Nat.cast_nonneg Q)]

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.RateExtraction

namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.RateExtraction
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence
open Qatlib.Foundations.FiniteStats.BornEstimator.ConfidenceLog

/-- The actual weak-spin survival log has a uniform elementary lower bound throughout the source excitation range. -/
theorem weak_survival_log (b : ℝ) (hb0 : 0≤b) (hb1 : b≤1/2) : -2*b≤Real.log (1-b) := by
  have hd : 0<1-b := by linarith
  have h := Real.one_sub_inv_le_log_of_pos hd
  have hf : b/(1-b)≤2*b := (div_le_iff₀ hd).2 (by nlinarith [mul_nonneg hb0 (by linarith : 0≤1-2*b)])
  have he : 1-(1-b)⁻¹=-(b/(1-b)) := by
    field_simp [ne_of_gt hd]
    ring
  rw [he] at h
  linarith

/-- The exact complete original dense-pair overlap pays the same confidence exponential at every natural copy budget. -/
theorem dense_survival_exp (b : ℝ) (hb0 : 0≤b) (hb1 : b≤1/2) (Q : ℕ) :
    Real.exp (-4*b*(Q : ℝ))≤(1-b)^(2*Q) := by
  have hl := mul_le_mul_of_nonneg_left (weak_survival_log b hb0 hb1) (show (0 : ℝ)≤((2*Q : ℕ) : ℝ) from Nat.cast_nonneg (2*Q))
  have hd : 0<1-b := by linarith
  calc
    _ ≤ Real.exp (((2*Q : ℕ) : ℝ)*Real.log (1-b)) := by
      apply Real.exp_le_exp.mpr
      push_cast at hl ⊢
      nlinarith
    _ = _ := by rw [Real.exp_nat_mul,Real.exp_log hd]

/-- Actual dense quantum testing yields the original N-squared logarithmic lower bound uniformly over every original confidence value. -/
theorem dense_information_rate (N Q : ℕ) (δ : ℝ) (hN : 256≤N) (hδ : 0<δ) (hmax : δ≤1/10)
    (hinfo : (1-128/((N : ℝ)^2))^(2*Q)≤8*δ) : (N : ℝ)^2*Real.log (1/δ)≤8192*(Q : ℝ) := by
  have hn : (N : ℝ)≠0 := by
    have h : (256 : ℝ)≤N := by exact_mod_cast hN
    linarith
  have hb := original_weak_excitation N hN
  have ht := (dense_survival_exp _ hb.1 hb.2 Q).trans hinfo
  have hl := Real.log_le_log (Real.exp_pos _) ht
  rw [Real.log_exp] at hl
  have hu := uniform_confidence_log δ hδ hmax
  have hi : Real.log (1/(8*δ))=-Real.log (8*δ) := by rw [one_div,Real.log_inv]
  rw [hi] at hu
  have hL : Real.log (1/δ)≤64*(128/((N : ℝ)^2))*(Q : ℝ) := by linarith
  have hm := mul_le_mul_of_nonneg_left hL (sq_nonneg (N : ℝ))
  have he : (N : ℝ)^2*(64*(128/((N : ℝ)^2))*(Q : ℝ))=8192*(Q : ℝ) := by
    field_simp [hn]
    ring
  rwa [he] at hm

/-- Beyond the original collision-confidence crossover, the same dense lower bound absorbs the full original square-root term. -/
theorem dense_sum_rate (N Q : ℕ) (M δ : ℝ) (hN : 256≤N) (hM : 0<M)
    (hδ : 0<δ) (hmax : δ≤1/10) (hlarge : M/(N : ℝ)^2≤Real.log (1/δ))
    (hinfo : (1-128/((N : ℝ)^2))^(2*Q)≤8*δ) :
    (N : ℝ)^2*Real.log (1/δ)+(N : ℝ)*Real.sqrt (M*Real.log (1/δ))≤131072*(Q : ℝ) := by
  have hn : 0<(N : ℝ)^2 := by
    have h : (256 : ℝ)≤N := by exact_mod_cast hN
    positivity
  have hL : 0≤Real.log (1/δ) := Real.log_nonneg ((le_div_iff₀ hδ).2 (by linarith))
  have hc := dense_information_rate N Q δ hN hδ hmax hinfo
  have hMbound : M≤(N : ℝ)^2*Real.log (1/δ) := by
    have h := (div_le_iff₀ hn).mp hlarge
    nlinarith
  have hnon : 0≤(N : ℝ)^2*Real.log (1/δ) := mul_nonneg hn.le hL
  have hs : ((N : ℝ)*Real.sqrt (M*Real.log (1/δ)))^2≤((N : ℝ)^2*Real.log (1/δ))^2 := by
    calc
      _ = (N : ℝ)^2*M*Real.log (1/δ) := by
        rw [mul_pow,Real.sq_sqrt (mul_nonneg hM.le hL)]
        ring
      _ = ((N : ℝ)^2*Real.log (1/δ))*M := by ring
      _ ≤ ((N : ℝ)^2*Real.log (1/δ))*((N : ℝ)^2*Real.log (1/δ)) := mul_le_mul_of_nonneg_left hMbound hnon
      _ = _ := by ring
  have hroot : 0≤(N : ℝ)*Real.sqrt (M*Real.log (1/δ)) := by positivity
  have hrt := (sq_le_sq₀ hroot hnon).mp hs
  nlinarith [hc,(show (0 : ℝ)≤(Q : ℝ) from Nat.cast_nonneg Q)]

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.RateExtraction
