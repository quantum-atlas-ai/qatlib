/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.IntervalCases
import Qatlib.Papers.SwitchAdiab12.MainResults.SourceCorollaryV2

set_option backward.isDefEq.respectTransparency false

/-!
# Double Convolution Bound for Switching Adiabatic Asymptotics (Corollary V.3)

This module formalizes Corollary V.3: for `α > 1` and `k ≥ 1`, summing the
binomial-weighted Gevrey product of Corollary V.2 against the quadratic weights
`((10n + 10.3 - 10i)^2 (10i + 0.3)^2)⁻¹` over `1 ≤ i ≤ n` and `0 ≤ k₁ ≤ k`
reproduces the Gevrey growth `(k + 3(n + 1))^{α(k + 3(n + 1))} / (10n + 10.3)^2`
with explicit contraction factor `0.05 * 4^{-(α - 3/2)} / (1 - 4^{-(α - 1)})`.

## Main statements

* `source_corollary_V3`: double sum bound Eq. (V.9) combining Corollary V.2,
  geometric tail summation, and the partial-fraction convolution bound Eq. (V.10).

## References

* [Elgart and Hagedorn, 2012][ElgartHagedorn2012SwitchAdiab], Appendix V,
  Corollary V.3, Eqs. (V.9)--(V.11), pp. 17--18.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SwitchAdiab12.MainResults.SourceCorollaryV3

open Finset

/-- Reflection of the positive indices in a finite interval. -/
private lemma sum_reflect (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Icc 1 n, f (n + 1 - i)) = ∑ i ∈ Icc 1 n, f i := by
  refine sum_nbij' (fun i ↦ n + 1 - i) (fun i ↦ n + 1 - i) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [mem_Icc] at hi ⊢
    omega
  · intro i hi
    simp only [mem_Icc] at hi ⊢
    omega
  · intro i hi
    simp only [mem_Icc] at hi
    omega
  · intro i hi
    simp only [mem_Icc] at hi
    omega
  · intro i _
    rfl

/-- Keep the first two terms, then telescope the reciprocal-square tail. -/
private lemma square_sum_tail (n : ℕ) (hn : 2 ≤ n) :
    (∑ i ∈ Icc 1 n, 1 / (10 * (i : ℝ) + 0.3) ^ 2) ≤ 0.017 - 0.01 / (n : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [sum_Icc_succ_top]
  | succ n hn ih =>
    rw [sum_Icc_succ_top (by omega)]
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have ht : 1 / (10 * ((n + 1 : ℕ) : ℝ) + 0.3) ^ 2 ≤
        0.01 / (n : ℝ) - 0.01 / ((n + 1 : ℕ) : ℝ) := by
      push_cast
      field_simp
      nlinarith
    push_cast at ht ⊢
    linarith

private lemma square_sum (n : ℕ) :
    (∑ i ∈ Icc 1 n, 1 / (10 * (i : ℝ) + 0.3) ^ 2) ≤ 0.017 := by
  by_cases hn : 2 ≤ n
  · exact (square_sum_tail n hn).trans (sub_le_self _ (by positivity))
  · interval_cases n <;> norm_num

/-- A rational linear bound for the reciprocal sum, starting at six. -/
private lemma reciprocal_sum (n : ℕ) (hn : 6 ≤ n) :
    (∑ i ∈ Icc 1 n, 1 / (10 * (i : ℝ) + 0.3)) ≤ (n : ℝ) / 70 + 223 / 1400 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [sum_Icc_succ_top]
  | succ n hn ih =>
    rw [sum_Icc_succ_top (by omega)]
    have hn' : (6 : ℝ) ≤ n := by exact_mod_cast hn
    have ht : 1 / (10 * ((n + 1 : ℕ) : ℝ) + 0.3) ≤ (1 : ℝ) / 70 := by
      apply one_div_le_one_div_of_le (by norm_num)
      push_cast
      linarith
    push_cast at ht ⊢
    linarith

/-- The rational partial-fraction estimate (V.10). -/
private lemma weight_sum (n : ℕ) :
    (∑ i ∈ Icc 1 n, 1 / ((10 * (n : ℝ) + 10.3 - 10 * (i : ℝ)) ^ 2 *
      (10 * (i : ℝ) + 0.3) ^ 2)) ≤ 0.05 / (10 * (n : ℝ) + 10.3) ^ 2 := by
  by_cases hn : 6 ≤ n
  · let S : ℝ := 10 * (n : ℝ) + 10.3
    let a : ℕ → ℝ := fun i ↦ 10 * (i : ℝ) + 0.3
    have hS : 0 < S := by dsimp [S]; positivity
    have ha (i : ℕ) : 0 < a i := by dsimp [a]; positivity
    have hb (i : ℕ) (hi : i ∈ Icc 1 n) : 0 < S - 10 * (i : ℝ) := by
      have hi' : (i : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hi).2
      dsimp [S]
      linarith
    have hpoint (i : ℕ) (hi : i ∈ Icc 1 n) :
        S ^ 2 * (1 / ((S - 10 * (i : ℝ)) ^ 2 * a i ^ 2)) ≤
        1 / a i ^ 2 + 1 / (S - 10 * (i : ℝ)) ^ 2 +
          (2 / (S + 0.3)) * (1 / a i + 1 / (S - 10 * (i : ℝ))) := by
      have he : a i + (S - 10 * (i : ℝ)) = S + 0.3 := by dsimp [a]; ring
      calc
        _ = S ^ 2 / ((S - 10 * (i : ℝ)) ^ 2 * a i ^ 2) := by ring
        _ ≤ (S + 0.3) ^ 2 / ((S - 10 * (i : ℝ)) ^ 2 * a i ^ 2) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          nlinarith
        _ = _ := by
          rw [← he]
          field_simp [(ha i).ne', (hb i hi).ne', (by linarith [ha i, hb i hi] : a i + (S - 10 * (i : ℝ)) ≠ 0)]
          ring
    have href (i : ℕ) (hi : i ∈ Icc 1 n) : S - 10 * (i : ℝ) = a (n + 1 - i) := by
      have hle : i ≤ n + 1 := (mem_Icc.mp hi).2.trans (Nat.le_succ n)
      dsimp [S, a]
      rw [Nat.cast_sub hle]
      push_cast
      ring
    have hsquare : (∑ i ∈ Icc 1 n, 1 / (S - 10 * (i : ℝ)) ^ 2) =
        ∑ i ∈ Icc 1 n, 1 / a i ^ 2 := by
      calc
        _ = ∑ i ∈ Icc 1 n, 1 / a (n + 1 - i) ^ 2 := sum_congr rfl (fun i hi ↦ by rw [href i hi])
        _ = _ := sum_reflect (fun i ↦ 1 / a i ^ 2) n
    have hrecip : (∑ i ∈ Icc 1 n, 1 / (S - 10 * (i : ℝ))) =
        ∑ i ∈ Icc 1 n, 1 / a i := by
      calc
        _ = ∑ i ∈ Icc 1 n, 1 / a (n + 1 - i) := sum_congr rfl (fun i hi ↦ by rw [href i hi])
        _ = _ := sum_reflect (fun i ↦ 1 / a i) n
    have ht := sum_le_sum hpoint
    simp only [sum_add_distrib, ← mul_sum, hsquare, hrecip] at ht
    have hsq : (∑ i ∈ Icc 1 n, 1 / a i ^ 2) ≤ 0.017 := square_sum n
    have hr : (∑ i ∈ Icc 1 n, 1 / a i) ≤ (n : ℝ) / 70 + 223 / 1400 := reciprocal_sum n hn
    have hc : (2 / (S + 0.3)) * (2 * ((n : ℝ) / 70 + 223 / 1400)) ≤ 0.015 := by
      have hn' : (6 : ℝ) ≤ n := by exact_mod_cast hn
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (by positivity : 0 < S + 0.3)).mpr
      dsimp [S]
      linarith
    have hr' := mul_le_mul_of_nonneg_left (add_le_add hr hr)
      (by positivity : 0 ≤ 2 / (S + 0.3))
    apply (le_div_iff₀ (sq_pos_of_pos hS)).mpr
    change (∑ i ∈ Icc 1 n, 1 / ((S - 10 * (i : ℝ)) ^ 2 * a i ^ 2)) * S ^ 2 ≤ 0.05
    nlinarith
  · interval_cases n <;> norm_num [sum_Icc_succ_top]

/-- The inner sum is bounded by two geometric tails, without a parity split. -/
private lemma geometric_min_sum (q : ℝ) (hq : 0 < q) (hq1 : q < 1) (k : ℕ) :
    (∑ j ∈ range (k + 1), q ^ (min (j + 1) (k - j + 1))) ≤ 2 * q / (1 - q) := by
  have ht (j : ℕ) : q ^ (min (j + 1) (k - j + 1)) ≤ q ^ (j + 1) + q ^ (k - j + 1) := by
    rcases le_total (j + 1) (k - j + 1) with h | h
    · rw [min_eq_left h]
      exact le_add_of_nonneg_right (pow_nonneg hq.le _)
    · rw [min_eq_right h]
      exact le_add_of_nonneg_left (pow_nonneg hq.le _)
  calc
    _ ≤ ∑ j ∈ range (k + 1), (q ^ (j + 1) + q ^ (k - j + 1)) := sum_le_sum (fun j _ ↦ ht j)
    _ = 2 * q * ∑ j ∈ range (k + 1), q ^ j := by
      rw [sum_add_distrib]
      have he : (∑ j ∈ range (k + 1), q ^ (k - j + 1)) = ∑ j ∈ range (k + 1), q ^ (j + 1) := by
        simpa only [Nat.add_sub_cancel] using sum_range_reflect (fun j ↦ q ^ (j + 1)) (k + 1)
      rw [he]
      simp only [pow_succ', ← mul_sum]
      ring
    _ = 2 * q * ((1 - q ^ (k + 1)) / (1 - q)) := by
      rw [geom_sum_eq hq1.ne]
      congr 1
      apply (div_eq_div_iff (sub_ne_zero.mpr hq1.ne) (sub_ne_zero.mpr hq1.ne')).mpr
      ring
    _ ≤ _ := by
      apply (le_div_iff₀ (sub_pos.mpr hq1)).mpr
      field_simp
      nlinarith [pow_pos hq (k + 1)]

/-- **Corollary V.3**: Gevrey double-convolution bound Eq. (V.9) for `α > 1`
and `k ≥ 1`. -/
theorem source_corollary_V3 (α : ℝ) (hα : 1 < α) (k n : ℕ) (hk : 1 ≤ k) :
    (∑ i ∈ Finset.Icc 1 n, ∑ k₁ ∈ Finset.range (k + 1),
        (1 / ((10 * (n : ℝ) + 10.3 - 10 * (i : ℝ)) ^ 2 *
            (10 * (i : ℝ) + 0.3) ^ 2)) *
          ((Nat.factorial k : ℝ) /
            ((Nat.factorial k₁ : ℝ) * (Nat.factorial (k - k₁) : ℝ))) *
          ((k₁ + 3 * (n + 1 - i) : ℕ) : ℝ) ^
            (α * ((k₁ + 3 * (n + 1 - i) : ℕ) : ℝ)) *
          ((k - k₁ + 3 * i : ℕ) : ℝ) ^
            (α * ((k - k₁ + 3 * i : ℕ) : ℝ)))
    ≤ (0.05 * (4 : ℝ) ^ (-(α - 3 / 2)) / (1 - (4 : ℝ) ^ (-(α - 1)))) *
      (((k + 3 * (n + 1) : ℕ) : ℝ) ^ (α * ((k + 3 * (n + 1) : ℕ) : ℝ))) /
        ((10 * (n : ℝ) + 10.3) ^ 2) := by
  refine (And.left ⟨?_, hk⟩)
  let q : ℝ := (4 : ℝ) ^ (-(α - 1))
  have hq : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  by_cases hn : n = 0
  · subst n
    simp only [Icc_eq_empty_of_lt (by omega : (0 : ℕ) < 1), sum_empty]
    exact div_nonneg (mul_nonneg (div_nonneg (by positivity) (sub_pos.mpr hq1).le)
      (by positivity)) (by positivity)
  · let M : ℝ := ((k + 3 * (n + 1) : ℕ) : ℝ) ^ (α * ((k + 3 * (n + 1) : ℕ) : ℝ))
    let w : ℕ → ℝ := fun i ↦ 1 / ((10 * (n : ℝ) + 10.3 - 10 * (i : ℝ)) ^ 2 *
      (10 * (i : ℝ) + 0.3) ^ 2)
    have hM : 0 ≤ M := by dsimp [M]; positivity
    have hw (i : ℕ) : 0 ≤ w i := by dsimp [w]; positivity
    have he (j : ℕ) : (4 : ℝ) ^ (-(α - 1) * ((min (j + 1) (k - j + 1) : ℕ) : ℝ)) =
        q ^ (min (j + 1) (k - j + 1)) := by
      dsimp [q]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
    have hinner (i : ℕ) (hi : i ∈ Icc 1 n) :
        (∑ j ∈ range (k + 1), w i *
          ((Nat.factorial k : ℝ) / ((Nat.factorial j : ℝ) * (Nat.factorial (k - j) : ℝ))) *
          ((j + 3 * (n + 1 - i) : ℕ) : ℝ) ^ (α * ((j + 3 * (n + 1 - i) : ℕ) : ℝ)) *
          ((k - j + 3 * i : ℕ) : ℝ) ^ (α * ((k - j + 3 * i : ℕ) : ℝ))) ≤
          w i * (2 * q / (1 - q)) * M := by
      have hi1 := (mem_Icc.mp hi).1
      have hin := (mem_Icc.mp hi).2
      calc
        _ ≤ ∑ j ∈ range (k + 1), w i * q ^ (min (j + 1) (k - j + 1)) * M := by
          apply sum_le_sum
          intro j hj
          have hjk : j ≤ k := by simpa only [mem_range, Nat.lt_succ_iff] using hj
          have hv := SourceCorollaryV2.source_corollary_V2 α hα.le j (k - j)
            (3 * n + 2) (by omega) (3 * i) (by omega) (by omega)
          have hsum : j + (k - j) = k := by omega
          have hleft : j + (3 * n + 2) + 1 - 3 * i = j + 3 * (n + 1 - i) := by omega
          have htotal : k + (3 * n + 2) + 1 = k + 3 * (n + 1) := by omega
          rw [hsum, hleft, htotal, he] at hv
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hv (hw i)
        _ = (w i * M) * (∑ j ∈ range (k + 1), q ^ (min (j + 1) (k - j + 1))) := by
          rw [mul_sum]
          apply sum_congr rfl
          intro j _
          ring
        _ ≤ (w i * M) * (2 * q / (1 - q)) :=
          mul_le_mul_of_nonneg_left (geometric_min_sum q hq hq1 k) (mul_nonneg (hw i) hM)
        _ = _ := by ring
    have hcoef : 2 * q = (4 : ℝ) ^ (-(α - 3 / 2)) := by
      have hh : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
        rw [← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      dsimp [q]
      rw [← hh, ← Real.rpow_add (by norm_num : (0 : ℝ) < 4)]
      congr 1
      ring
    calc
      _ ≤ ∑ i ∈ Icc 1 n, w i * (2 * q / (1 - q)) * M := sum_le_sum hinner
      _ = (∑ i ∈ Icc 1 n, w i) * (2 * q / (1 - q)) * M := by rw [sum_mul, sum_mul]
      _ ≤ (0.05 / (10 * (n : ℝ) + 10.3) ^ 2) * (2 * q / (1 - q)) * M := by
        apply mul_le_mul_of_nonneg_right _ hM
        exact mul_le_mul_of_nonneg_right (weight_sum n) (by positivity)
      _ = _ := by rw [hcoef]; dsimp [q, M]; ring

end Qatlib.Papers.SwitchAdiab12.MainResults.SourceCorollaryV3

#lint only unusedArguments
