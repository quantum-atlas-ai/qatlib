/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace Qatlib.Concepts.FinitePrecision.ComputableInput.FiniteWeights

def count (scale numerator denominator : ℕ) : ℕ :=
  scale * min numerator denominator / denominator

noncomputable def finiteValue (numerator denominator : ℕ) : ℝ :=
  (min numerator denominator : ℕ) / (denominator : ℝ)

noncomputable def rounded (scale numerator denominator : ℕ) : ℝ :=
  (count scale numerator denominator : ℝ) / (scale : ℝ)

theorem rounded_bounds (scale numerator denominator : ℕ)
    (hscale : 0 < scale) (hden : 0 < denominator) :
    rounded scale numerator denominator ≤ finiteValue numerator denominator ∧
    finiteValue numerator denominator < rounded scale numerator denominator + 1/(scale : ℝ) := by
  have hs : (0 : ℝ) < scale := by exact_mod_cast hscale
  have hd : (0 : ℝ) < denominator := by exact_mod_cast hden
  have hlo : count scale numerator denominator * denominator ≤ scale * min numerator denominator :=
    Nat.div_mul_le_self _ _
  have hhi : scale * min numerator denominator < (count scale numerator denominator + 1)*denominator :=
    (Nat.div_lt_iff_lt_mul hden).mp (Nat.lt_succ_self _)
  have hl :
      (count scale numerator denominator : ℝ) * denominator ≤
      (scale : ℝ) * min numerator denominator := by exact_mod_cast hlo
  have hh :
      (scale : ℝ) * min numerator denominator <
      ((count scale numerator denominator : ℝ)+1)*denominator := by exact_mod_cast hhi
  unfold rounded finiteValue
  constructor
  · apply (div_le_div_iff₀ hs hd).mpr
    nlinarith
  · rw [← add_div]
    apply (div_lt_div_iff₀ hd hs).mpr
    nlinarith

theorem count_le (scale numerator denominator : ℕ) (hden : 0 < denominator) :
    count scale numerator denominator ≤ scale := by
  by_cases hz : scale = 0
  · simp [count, hz]
  have hs : 0 < scale := Nat.pos_of_ne_zero hz
  have hdR : (0 : ℝ) < denominator := by exact_mod_cast hden
  have hsR : (0 : ℝ) < scale := by exact_mod_cast hs
  have hv : finiteValue numerator denominator ≤ 1 := by
    apply (div_le_one hdR).mpr
    exact_mod_cast Nat.min_le_right numerator denominator
  have hb := (rounded_bounds scale numerator denominator hs hden).1.trans hv
  have hc : (count scale numerator denominator : ℝ) ≤ scale := (div_le_one hsR).mp hb
  exact_mod_cast hc

variable {I : Type*} [Fintype I]

theorem mass_error (t q : I → ℝ) (hq : ∑ i, q i = 1) :
    |(∑ i, t i)-1| ≤ ∑ i, |t i-q i| := by
  rw [← hq, ← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _

theorem normalized_l1 (t q : I → ℝ) (ht : ∀ i, 0 ≤ t i)
    (hq : ∑ i, q i = 1) (hZ : 0 < ∑ i, t i) :
    (∑ i, |t i/(∑ j, t j)-q i|) ≤ 2*(∑ i, |t i-q i|) := by
  let Z := ∑ i, t i
  have hZ0 : Z ≠ 0 := ne_of_gt hZ
  have hnorm : (∑ i, |t i/Z-t i|) = |1-Z| := by
    have he (i : I) : |t i/Z-t i| = (|1-Z|/Z)*t i := by
      rw [show t i/Z-t i = ((1-Z)/Z)*t i by field_simp, abs_mul,
        abs_div, abs_of_pos hZ, abs_of_nonneg (ht i)]
    simp_rw [he]
    rw [← Finset.mul_sum]
    change |1-Z|/Z*Z = _
    exact div_mul_cancel₀ _ hZ0
  calc
    _ ≤ ∑ i, (|t i/Z-t i|+|t i-q i|) := by
      apply Finset.sum_le_sum
      intro i _
      simpa using abs_add_le (t i/Z-t i) (t i-q i)
    _ = |1-Z|+∑ i, |t i-q i| := by rw [Finset.sum_add_distrib, hnorm]
    _ ≤ 2*(∑ i, |t i-q i|) := by
      have he := mass_error t q hq
      have hflip : |1-Z| = |Z-1| := abs_sub_comm _ _
      rw [hflip]
      linarith

theorem sqrt_sq_le_abs (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (Real.sqrt u-Real.sqrt v)^2 ≤ |u-v| := by
  have hsu := Real.sqrt_nonneg u
  have hsv := Real.sqrt_nonneg v
  have hqu := Real.sq_sqrt hu
  have hqv := Real.sq_sqrt hv
  rcases le_total u v with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    have hh := Real.sqrt_le_sqrt h
    nlinarith [mul_nonneg hsu (sub_nonneg.mpr hh)]
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    have hh := Real.sqrt_le_sqrt h
    nlinarith [mul_nonneg hsv (sub_nonneg.mpr hh)]

theorem normalized_counts_endpoint (numerator denominator : I → ℕ)
    (scale : ℕ) (hs : 0 < scale) (hd : ∀ i, 0 < denominator i)
    (q : I → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1)
    (alpha : ℝ) (ha : ∀ i, |finiteValue (numerator i) (denominator i)-q i| ≤ alpha)
    (hsmall : (Fintype.card I : ℝ)*(alpha+1/(scale : ℝ)) < 1) :
    let t := fun i => rounded scale (numerator i) (denominator i)
    let Z := ∑ i, t i
    0 < Z ∧ (∑ i, t i/Z) = 1 ∧ (∀ i, 0 ≤ t i/Z) ∧
      (∑ i, (Real.sqrt (t i/Z)-Real.sqrt (q i))^2) ≤
        2*(Fintype.card I : ℝ)*(alpha+1/(scale : ℝ)) := by
  dsimp only
  let t := fun i => rounded scale (numerator i) (denominator i)
  let Z := ∑ i, t i
  let e := alpha+1/(scale : ℝ)
  have ht (i : I) : 0 ≤ t i := by dsimp [t, rounded]; positivity
  have hpoint (i : I) : |t i-q i| ≤ e := by
    have hb := rounded_bounds scale (numerator i) (denominator i) hs (hd i)
    have herr : |t i-finiteValue (numerator i) (denominator i)| ≤ 1/(scale : ℝ) := by
      apply abs_le.mpr
      dsimp only [t]
      constructor <;> linarith [hb.1, hb.2]
    calc
      _ = |(t i-finiteValue (numerator i) (denominator i))+
          (finiteValue (numerator i) (denominator i)-q i)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ e := by dsimp [e]; linarith [ha i]
  have hsum : (∑ i, |t i-q i|) ≤ (Fintype.card I : ℝ)*e := by
    calc
      _ ≤ ∑ _i : I, e := Finset.sum_le_sum (fun i _ => hpoint i)
      _ = _ := by simp
  have hZ : 0 < Z := by
    have hm := (mass_error t q hq1).trans hsum
    have hl := (abs_le.mp hm).1
    dsimp only [Z]
    dsimp only [e] at hl
    linarith
  refine ⟨hZ, ?_, ?_, ?_⟩
  · rw [← Finset.sum_div]
    exact div_self (ne_of_gt hZ)
  · intro i
    exact div_nonneg (ht i) (le_of_lt hZ)
  · calc
      _ ≤ ∑ i, |t i/Z-q i| := Finset.sum_le_sum
        (fun i _ => sqrt_sq_le_abs _ _ (div_nonneg (ht i) (le_of_lt hZ)) (hq0 i))
      _ ≤ 2*(∑ i, |t i-q i|) := normalized_l1 t q ht hq1 hZ
      _ ≤ _ := by dsimp only [e] at hsum; linarith
end Qatlib.Concepts.FinitePrecision.ComputableInput.FiniteWeights
