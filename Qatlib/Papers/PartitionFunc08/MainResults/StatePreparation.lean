/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.PartitionFunc08.MainResults.StatePreparation

variable {Ω : Type*} [Fintype Ω]

noncomputable def gibbsWeight (β : ℝ) (E : Ω → ℝ) (σ : Ω) : ℝ :=
  Real.exp (-(β * E σ))

noncomputable def gibbsPartition (β : ℝ) (E : Ω → ℝ) : ℝ :=
  ∑ σ, gibbsWeight β E σ

noncomputable def gibbsOverlapSq (β β' : ℝ) (E : Ω → ℝ) : ℝ :=
  (∑ σ, Real.sqrt (gibbsWeight β E σ * gibbsWeight β' E σ)) ^ 2 /
    (gibbsPartition β E * gibbsPartition β' E)

theorem gibbs_overlap_ge_half (E : Ω → ℝ) (hE : ∀ σ, 0 ≤ E σ) {β β' : ℝ} (hβ : β ≤ β')
    (hZ0 : 0 < gibbsPartition β E) (hZ1 : 0 < gibbsPartition β' E)
    (hα : gibbsPartition β E ≤ 2 * gibbsPartition β' E) :
    1 / 2 ≤ gibbsOverlapSq β β' E := by
  classical
  have hterm : ∀ σ, gibbsWeight β' E σ ≤
      Real.sqrt (gibbsWeight β E σ * gibbsWeight β' E σ) := by
    intro σ
    have hprod : gibbsWeight β E σ * gibbsWeight β' E σ =
        Real.exp (-((β + β') * E σ)) := by
      have harg : -(β * E σ) + -(β' * E σ) = -((β + β') * E σ) := by ring
      calc gibbsWeight β E σ * gibbsWeight β' E σ
          = Real.exp (-(β * E σ)) * Real.exp (-(β' * E σ)) := by
            simp only [gibbsWeight]
        _ = Real.exp (-(β * E σ) + -(β' * E σ)) := by rw [← Real.exp_add]
        _ = Real.exp (-((β + β') * E σ)) := by rw [harg]
    have hhalf : Real.exp (-((β + β') * E σ)) =
        (Real.exp (-(((β + β') * E σ) / 2))) ^ 2 := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    rw [hprod, hhalf, Real.sqrt_sq (Real.exp_nonneg _)]
    simp only [gibbsWeight]
    apply Real.exp_le_exp.mpr
    have hEσ := hE σ
    nlinarith
  have hsum : gibbsPartition β' E ≤
      ∑ σ, Real.sqrt (gibbsWeight β E σ * gibbsWeight β' E σ) :=
    Finset.sum_le_sum (fun σ _ => hterm σ)
  have hsum_nonneg : 0 ≤ ∑ σ, Real.sqrt (gibbsWeight β E σ * gibbsWeight β' E σ) :=
    Finset.sum_nonneg (fun σ _ => Real.sqrt_nonneg _)
  have hsq : (gibbsPartition β' E) ^ 2 ≤
      (∑ σ, Real.sqrt (gibbsWeight β E σ * gibbsWeight β' E σ)) ^ 2 :=
    pow_le_pow_left₀ hZ1.le hsum 2
  unfold gibbsOverlapSq
  rw [le_div_iff₀ (mul_pos hZ0 hZ1)]
  have hstep1 : gibbsPartition β E * gibbsPartition β' E ≤
      2 * (gibbsPartition β' E) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hα hZ1.le
    calc gibbsPartition β E * gibbsPartition β' E
        ≤ (2 * gibbsPartition β' E) * gibbsPartition β' E := h1
      _ = 2 * (gibbsPartition β' E) ^ 2 := by ring
  linarith [hstep1, hsq]

theorem sqrt_prob_diff_le {p q εS : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) (hεS : 0 ≤ εS) (h : |Real.sqrt p - Real.sqrt q| ≤ εS) :
    |p - q| ≤ 2 * εS := by
  have hsp : (Real.sqrt p) ^ 2 = p := Real.sq_sqrt hp0
  have hsq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq0
  have hfac : p - q = (Real.sqrt p - Real.sqrt q) * (Real.sqrt p + Real.sqrt q) := by
    calc p - q = (Real.sqrt p) ^ 2 - (Real.sqrt q) ^ 2 := by rw [hsp, hsq]
      _ = (Real.sqrt p - Real.sqrt q) * (Real.sqrt p + Real.sqrt q) := by ring
  have hsp1 : Real.sqrt p ≤ 1 := Real.sqrt_le_one.mpr hp1
  have hsq1 : Real.sqrt q ≤ 1 := Real.sqrt_le_one.mpr hq1
  have hspn := Real.sqrt_nonneg p
  have hsqn := Real.sqrt_nonneg q
  rw [hfac, abs_mul]
  have hsum : |Real.sqrt p + Real.sqrt q| ≤ 2 := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  calc |Real.sqrt p - Real.sqrt q| * |Real.sqrt p + Real.sqrt q|
      ≤ εS * 2 := mul_le_mul h hsum (abs_nonneg _) hεS
    _ = 2 * εS := by ring

theorem lemma4_state_preparation (E : Ω → ℝ) (hE : ∀ σ, 0 ≤ E σ) {β β' : ℝ} (hβ : β ≤ β')
    (hZ0 : 0 < gibbsPartition β E) (hZ1 : 0 < gibbsPartition β' E)
    (hα : gibbsPartition β E ≤ 2 * gibbsPartition β' E) {εS : ℝ} (hεS : 0 ≤ εS) :
    1 / 2 ≤ gibbsOverlapSq β β' E ∧
      ∀ p q : ℝ, 0 ≤ p → p ≤ 1 → 0 ≤ q → q ≤ 1 →
        |Real.sqrt p - Real.sqrt q| ≤ εS → |p - q| ≤ 2 * εS :=
  ⟨gibbs_overlap_ge_half E hE hβ hZ0 hZ1 hα,
    fun p q hp0 hp1 hq0 hq1 h => sqrt_prob_diff_le hp0 hp1 hq0 hq1 hεS h⟩

end Qatlib.Papers.PartitionFunc08.MainResults.StatePreparation
