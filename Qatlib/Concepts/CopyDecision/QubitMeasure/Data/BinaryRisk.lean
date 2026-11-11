/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyDecision.QubitMeasure.Data.BinaryPosterior

/-!
# Binary Risk

Qubit Measure constructions for Copy Decision.
Defines `binaryRisk`.
Proves `binaryRisk_zero`, `binaryRisk_depth_zero`, `binaryRadicand_nonneg`.
-/


set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.CopyDecision.QubitMeasure.Data
open Qatlib.Concepts.CopyDecision.FreshPolicies.Data Qatlib.Foundations.DecisionRisk.HarmonicError

/-- Definition of binary Risk in the Qubit Measure construction. -/
def binaryRisk (n : ℕ) (p q : ℝ) : ℝ :=
  (p+q-Real.sqrt ((p+q)^2-4*p*q*(1/4:ℝ)^n))/2

/-- The stated copy-decision construction satisfies `binaryRisk_zero` with the complete displayed premises. -/
lemma binaryRisk_zero (n : ℕ) : binaryRisk n 0 0=0 := by simp [binaryRisk]

/-- The stated copy-decision construction satisfies `binaryRisk_depth_zero` with the complete displayed premises. -/
lemma binaryRisk_depth_zero (p q : ℝ) : binaryRisk 0 p q=min p q := by
  have he : (p+q)^2-4*p*q=(p-q)^2 := by ring
  simp only [binaryRisk, pow_zero, mul_one, he, Real.sqrt_sq_eq_abs]
  by_cases h : p ≤ q
  · rw [abs_of_nonpos (sub_nonpos.mpr h), min_eq_left h]
    ring
  · rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge h)), min_eq_right (le_of_not_ge h)]
    ring

/-- The stated copy-decision construction satisfies `binaryRadicand_nonneg` with the complete displayed premises. -/
lemma binaryRadicand_nonneg (n : ℕ) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    0 ≤ (p+q)^2-4*p*q*(1/4:ℝ)^n := by
  have hpow : (1/4:ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hmul := mul_le_mul_of_nonneg_left hpow (show (0:ℝ) ≤ 4*p*q by positivity)
  nlinarith [sq_nonneg (p-q)]

/-- The actual posterior-product identity determines the next risk radicand,
without dividing by branch mass. Only the positive parent mass is divided. -/
lemma binaryRisk_sqrt_branch (n : ℕ) {p q r s : ℝ} (hQ : 0 < p+q)
    (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hprod : 4*(p+q)^2*r*s=p*q*(r+s)^2) :
    Real.sqrt ((r+s)^2-4*r*s*(1/4:ℝ)^n)=
      ((r+s)/(p+q))*Real.sqrt ((p+q)^2-4*p*q*(1/4:ℝ)^(n+1)) := by
  have hQ2 : (p+q)^2≠0 := pow_ne_zero _ (ne_of_gt hQ)
  have he : ((r+s)^2-4*r*s*(1/4:ℝ)^n)*(p+q)^2=
      (r+s)^2*((p+q)^2-4*p*q*(1/4:ℝ)^(n+1)) := by
    rw [pow_succ]
    linear_combination -(1/4:ℝ)^n*hprod
  have hscale : (r+s)^2-4*r*s*(1/4:ℝ)^n=
      ((r+s)/(p+q))^2*((p+q)^2-4*p*q*(1/4:ℝ)^(n+1)) := by
    calc
      _ = ((r+s)^2*((p+q)^2-4*p*q*(1/4:ℝ)^(n+1)))/(p+q)^2 :=
        (eq_div_iff hQ2).2 he
      _ = _ := by field_simp [ne_of_gt hQ]
  rw [hscale, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (div_nonneg (add_nonneg hr hs) hQ.le)]

/-- Achieved-risk Bellman identity from mass conservation and the ACTUAL
posterior product, including branches of zero mass. -/
theorem binaryRisk_sum {α : Type*} [Fintype α] (n : ℕ) (p q : ℝ) (hQ : 0 < p+q)
    (r s : α → ℝ) (hr : ∀ a, 0 ≤ r a) (hs : ∀ a, 0 ≤ s a)
    (hmass : ∑ a, (r a+s a)=p+q)
    (hprod : ∀ a, 4*(p+q)^2*r a*s a=p*q*(r a+s a)^2) :
    (∑ a, binaryRisk n (r a) (s a))=binaryRisk (n+1) p q := by
  simp only [binaryRisk]
  simp_rw [binaryRisk_sqrt_branch n hQ (hr _) (hs _) (hprod _)]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, hmass, ← Finset.sum_mul, ← Finset.sum_div, hmass]
  rw [div_self (ne_of_gt hQ), one_mul]

end Qatlib.Concepts.CopyDecision.QubitMeasure.Data
