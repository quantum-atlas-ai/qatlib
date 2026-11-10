/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Foundations.CostRecurrences.FiniteWeights

theorem sum_cube_le_cube_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) :
    (∑ i ∈ s, a i ^ 3) ≤ (∑ i ∈ s, a i) ^ 3 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx]
      have hxs : ∀ i ∈ s, 0 ≤ a i := fun i hi => ha i (Finset.mem_insert.mpr (Or.inr hi))
      have hx0 : 0 ≤ a x := ha x (Finset.mem_insert.mpr (Or.inl rfl))
      have hsum0 : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg hxs
      have hih := ih hxs

      have key : (∑ i ∈ s, a i) ^ 3 + a x ^ 3 ≤ ((∑ i ∈ s, a i) + a x) ^ 3 := by
        have h1 : (0 : ℝ) ≤ 3 * (∑ i ∈ s, a i) ^ 2 * a x := by positivity
        have h2 : (0 : ℝ) ≤ 3 * (∑ i ∈ s, a i) * a x ^ 2 := by positivity
        nlinarith [h1, h2]
      linarith [hih, key]

theorem weighted_cube_bound {ι : Type*} (s : Finset ι) (a b c : ι → ℝ)
    (L B Cc : ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb0 : ∀ i ∈ s, 0 ≤ b i) (hbB : ∀ i ∈ s, b i ≤ B)
    (hc0 : ∀ i ∈ s, 0 ≤ c i) (hcC : ∀ i ∈ s, c i ≤ Cc)
    (hB0 : 0 ≤ B) (hCc0 : 0 ≤ Cc)
    (hL : (∑ i ∈ s, a i) ≤ L) :
    (∑ i ∈ s, a i ^ 3 * b i ^ 2 * c i) ≤ L ^ 3 * B ^ 2 * Cc := by
  classical

  have hterm : ∀ i ∈ s, a i ^ 3 * b i ^ 2 * c i ≤ a i ^ 3 * B ^ 2 * Cc := by
    intro i hi
    have ha3 : 0 ≤ a i ^ 3 := pow_nonneg (ha i hi) 3
    have hb2 : b i ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (hb0 i hi) (hbB i hi) 2
    have h1 : a i ^ 3 * b i ^ 2 ≤ a i ^ 3 * B ^ 2 :=
      mul_le_mul_of_nonneg_left hb2 ha3
    exact mul_le_mul h1 (hcC i hi) (hc0 i hi) (mul_nonneg ha3 (pow_nonneg hB0 2))
  have hsum_le : (∑ i ∈ s, a i ^ 3 * b i ^ 2 * c i) ≤
      (∑ i ∈ s, a i ^ 3 * B ^ 2 * Cc) := Finset.sum_le_sum hterm

  have hfactor : (∑ i ∈ s, a i ^ 3 * B ^ 2 * Cc) =
      (B ^ 2 * Cc) * (∑ i ∈ s, a i ^ 3) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)

  have hsum0 : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg ha
  have hcube_sum : (∑ i ∈ s, a i ^ 3) ≤ (∑ i ∈ s, a i) ^ 3 :=
    sum_cube_le_cube_sum s a ha
  have hcube_mono : (∑ i ∈ s, a i) ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ hsum0 hL 3
  have hfin : (B ^ 2 * Cc) * (∑ i ∈ s, a i ^ 3) ≤ (B ^ 2 * Cc) * L ^ 3 :=
    mul_le_mul_of_nonneg_left (le_trans hcube_sum hcube_mono) (mul_nonneg (pow_nonneg hB0 2) hCc0)
  calc
    (∑ i ∈ s, a i ^ 3 * b i ^ 2 * c i) ≤ (B ^ 2 * Cc) * (∑ i ∈ s, a i ^ 3) := by
      rw [← hfactor]; exact hsum_le
    _ ≤ (B ^ 2 * Cc) * L ^ 3 := hfin
    _ = L ^ 3 * B ^ 2 * Cc := by ring

theorem log_prod_le_sum_sub_one {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) :
    Real.log (∏ i ∈ s, a i) ≤ ∑ i ∈ s, (a i - 1) := by
  rw [Real.log_prod (fun i hi => (ha i hi).ne')]
  exact Finset.sum_le_sum (fun i hi => Real.log_le_sub_one_of_pos (ha i hi))

end Qatlib.Foundations.CostRecurrences.FiniteWeights
