/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.WeightEnum07.MainResults.Theorem13
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Precision bounds for exact weight recovery

This module propagates componentwise approximation errors through finite weighted sums and the
affine weight formula. The resulting half-spacing estimate supports
`weightCounts_exact_of_precision`, which recovers exact weight multiplicities by rounding to a
known integer lattice.

This development forms part of the formalization of [GeraciVanBussel2007].

## Main statements

* `weight_error_lt_half`: Under the stated positivity, parameter, and precision assumptions, the
  scaled error expression is strictly less than `L / 2`.
* `weightCounts_exact_of_precision`: If all word weights are divisible by positive `L` and
  approximations are within `L / 2`, lattice rounding recovers the entire exact weight-count
  function.

## References

* [Geraci and Van Bussel, 2007][GeraciVanBussel2007]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.WeightEnum07.GaussRecovery

open scoped BigOperators
open Qatlib.Papers.WeightEnum07.MainResults

/-- If coefficients have absolute value at most one and each approximation error is at most `B`,
the weighted-sum error is at most `s.card * B`. -/
theorem abs_sum_mul_sub_le {ι : Type*} (s : Finset ι) (χ G Ĝ : ι → ℝ) {B : ℝ}
    (hχ : ∀ i ∈ s, |χ i| ≤ 1)
    (h : ∀ i ∈ s, |G i - Ĝ i| ≤ B) :
    |∑ i ∈ s, χ i * G i - ∑ i ∈ s, χ i * Ĝ i| ≤ s.card * B := by
  classical
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ i ∈ s, |χ i * G i - χ i * Ĝ i| ≤ B := by
    intro i hi
    rw [← mul_sub, abs_mul]
    calc |χ i| * |G i - Ĝ i| ≤ 1 * |G i - Ĝ i| :=
          mul_le_mul_of_nonneg_right (hχ i hi) (abs_nonneg _)
      _ ≤ 1 * B := mul_le_mul_of_nonneg_left (h i hi) zero_le_one
      _ = B := by ring
  calc |∑ i ∈ s, (χ i * G i - χ i * Ĝ i)|
        ≤ ∑ i ∈ s, |χ i * G i - χ i * Ĝ i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, B := Finset.sum_le_sum hterm
    _ = s.card * B := by rw [Finset.sum_const, nsmul_eq_mul]

/-- Multiplying the weighted-sum formula by a nonnegative scale `c` bounds its error by `c *
(s.card * B)`. -/
theorem weight_error_bound {ι : Type*} (s : Finset ι) (C c : ℝ) (χ G Ĝ : ι → ℝ) {B : ℝ}
    (hc : 0 ≤ c) (hχ : ∀ i ∈ s, |χ i| ≤ 1)
    (h : ∀ i ∈ s, |G i - Ĝ i| ≤ B) :
    |(C - c * ∑ i ∈ s, χ i * G i) - (C - c * ∑ i ∈ s, χ i * Ĝ i)| ≤ c * (s.card * B) := by
  have hsum := abs_sum_mul_sub_le s χ G Ĝ hχ h
  have hdiff : (C - c * ∑ i ∈ s, χ i * G i) - (C - c * ∑ i ∈ s, χ i * Ĝ i)
      = -(c * (∑ i ∈ s, χ i * G i - ∑ i ∈ s, χ i * Ĝ i)) := by ring
  rw [hdiff, abs_neg, abs_mul, abs_of_nonneg hc]
  calc c * |∑ i ∈ s, χ i * G i - ∑ i ∈ s, χ i * Ĝ i| ≤ c * (s.card * B) :=
        mul_le_mul_of_nonneg_left hsum hc

/-- Under the stated positivity, parameter, and precision assumptions, the scaled error
expression is strictly less than `L / 2`. See [GeraciVanBussel2007]. -/
theorem weight_error_lt_half {q N d : ℕ} {L Q ε : ℝ}
    (hq : 0 < q) (hdpos : 0 < d) (hN : 0 < N) (hQ : 0 < Q) (hL : 0 < L)
    (hd : ((q : ℝ) - 1) * ((d : ℝ) - 1) < (q : ℝ) * N)
    (hprec : ε ≤ L / (4 * Real.sqrt Q)) :
    ((q : ℝ) - 1) / ((q : ℝ) * N) * (((d : ℝ) - 1) * (Real.sqrt Q * ε)) < L / 2 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqN : (0 : ℝ) < (q : ℝ) * N := mul_pos hqR (by exact_mod_cast hN)
  have hs : (0 : ℝ) < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hq1 : (0 : ℝ) ≤ (q : ℝ) - 1 := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hd1 : (0 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hdpos
    linarith
  have hcoef : (0 : ℝ) ≤ ((q : ℝ) - 1) / ((q : ℝ) * N) := div_nonneg hq1 (le_of_lt hqN)

  have hstep : Real.sqrt Q * ε ≤ Real.sqrt Q * (L / (4 * Real.sqrt Q)) :=
    mul_le_mul_of_nonneg_left hprec (le_of_lt hs)
  have hcancel : Real.sqrt Q * (L / (4 * Real.sqrt Q)) = L / 4 := by
    field_simp
  rw [hcancel] at hstep
  have hstep' : ((d : ℝ) - 1) * (Real.sqrt Q * ε) ≤ ((d : ℝ) - 1) * (L / 4) :=
    mul_le_mul_of_nonneg_left hstep hd1
  have hmain : ((q : ℝ) - 1) / ((q : ℝ) * N) * (((d : ℝ) - 1) * (Real.sqrt Q * ε))
      ≤ ((q : ℝ) - 1) / ((q : ℝ) * N) * (((d : ℝ) - 1) * (L / 4)) :=
    mul_le_mul_of_nonneg_left hstep' hcoef
  have hratio : ((q : ℝ) - 1) * ((d : ℝ) - 1) / ((q : ℝ) * N) < 1 := by
    rw [div_lt_one hqN]
    exact hd
  have hquarter : (0 : ℝ) < L / 4 := by linarith
  have hlt : ((q : ℝ) - 1) * ((d : ℝ) - 1) / ((q : ℝ) * N) * (L / 4) < L / 4 := by
    nlinarith [hratio, hquarter]
  have heq : ((q : ℝ) - 1) / ((q : ℝ) * N) * (((d : ℝ) - 1) * (L / 4))
      = ((q : ℝ) - 1) * ((d : ℝ) - 1) / ((q : ℝ) * N) * (L / 4) := by
    field_simp
  rw [heq] at hmain
  linarith

/-- If all word weights are divisible by positive `L` and approximations are within `L / 2`,
lattice rounding recovers the entire exact weight-count function. See [GeraciVanBussel2007]. -/
theorem weightCounts_exact_of_precision {n : ℕ} (words : Finset (Fin n → ℤ))
    (approx : (Fin n → ℤ) → ℝ) {L : ℕ} (hL : 0 < L)
    (hdiv : ∀ w ∈ words, (L : ℤ) ∣ (hammingWeightOf w : ℤ))
    (hclose : ∀ w ∈ words, |approx w - (hammingWeightOf w : ℝ)| < (L : ℝ) / 2) :
    (fun i : ℕ => (words.filter (fun w => roundToLattice L (approx w) = (i : ℤ))).card) =
      (fun i : ℕ => (words.filter (fun w => hammingWeightOf w = i)).card) := by
  funext i
  exact weightCount_round_eq words approx hL hdiv hclose i

end Qatlib.Papers.WeightEnum07.GaussRecovery
