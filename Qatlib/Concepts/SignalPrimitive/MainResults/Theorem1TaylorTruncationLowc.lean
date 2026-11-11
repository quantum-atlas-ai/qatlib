/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SignalPrimitive.MainResults.Theorem1TaylorTruncationStat
import Qatlib.Concepts.SignalPrimitive.MainResults.TaylorTruncation
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Qatlib.Concepts.QspSimulation.Achievability.ExponentialPolynomial

/-!
# Corrected Taylor Truncation Degree

This module proves `theorem1TaylorTruncation`, the corrected Taylor degree guarantee used by the
encoded simulation construction associated with [LowChuang2019]. For every real `τ` and positive
`ε`, it supplies a natural cutoff `n` satisfying `2 * |τ| ≤ n + 1` and `exponentialTaylorError τ
n ≤ ε`.

The proof works with `δ = min ε 1` and chooses a cutoff using a ceiling of `4 * |τ| + 2 * log (2
/ δ)`. It establishes the stated budget `n ≤ 4 * |τ| + 8 * log (8 / min ε 1) + 8`, which remains
meaningful for large tolerances.

## Main statements

- `theorem1TaylorTruncation` proves the corrected cutoff, error, and degree bounds.

## References

- [Low and Chuang, 2019][LowChuang2019], Theorem 1.
-/

set_option warningAsError false
open Qatlib.Concepts.QspSimulation.Achievability

set_option autoImplicit false

namespace Qatlib.Concepts.SignalPrimitive.MainResults
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib

/-- Proves the corrected Taylor truncation contract for every positive tolerance, using `min ε
1` in the logarithmic degree budget. The cutoff supplies the scalar approximation bound used
for the simulation construction associated with Theorem 1 of [LowChuang2019]. -/
theorem theorem1TaylorTruncation : Theorem1TaylorTruncation := by
  intro τ ε hε
  let δ := min ε 1
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδε : δ ≤ ε := min_le_left _ _
  have hlog : 0 ≤ Real.log (2 / δ) := Real.log_nonneg ((one_le_div hδ).2 (by linarith))
  have hlog8 : Real.log (2 / δ) ≤ Real.log (8 / δ) :=
    Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by norm_num) hδ.le)
  have hlog2 : (1/2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : 0 < (2 : ℝ)⁻¹)
    rw [Real.log_inv] at hh
    norm_num at hh
    linarith
  let a := 4 * |τ| + 2 * Real.log (2 / δ)
  let n := Nat.ceil a + 1
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hn : a ≤ (n : ℝ) := by
    have hh := Nat.le_ceil a
    dsimp [n]
    push_cast
    linarith
  have hnu : (n : ℝ) < a + 2 := by
    have hh := Nat.ceil_lt_add_one ha
    dsimp [n]
    push_cast
    linarith
  have hnlog : 2 * |τ| + Real.log (2 / δ) ≤ (n : ℝ) * Real.log 2 := by
    have hh := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg n)
    dsimp [a] at hn
    linarith
  refine ⟨n, ?_, ?_, ?_⟩
  · dsimp [a] at hn
    linarith [abs_nonneg τ]
  · have hh := Real.pow_div_factorial_le_exp (2 * |τ|) (by positivity : 0 ≤ 2 * |τ|) n
    have hb := div_le_div_of_nonneg_right hh (by positivity : 0 ≤ (2 : ℝ)^n)
    have heq : (2 * |τ|)^n / (n.factorial : ℝ) / (2 : ℝ)^n =
        |τ|^n / (n.factorial : ℝ) := by
      rw [mul_pow]
      field_simp
    rw [heq] at hb
    have htail : exponentialTaylorError τ n ≤ 2 * Real.exp (2 * |τ|) / (2 : ℝ)^n := by
      unfold exponentialTaylorError
      convert! mul_le_mul_of_nonneg_right hb (by norm_num : (0 : ℝ) ≤ 2) using 1
      ring
    have hexp : 2 * Real.exp (2 * |τ|) / (2 : ℝ)^n =
        2 * Real.exp (2 * |τ| - (n : ℝ) * Real.log 2) := by
      rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log (by norm_num : 0 < (2 : ℝ))]
      ring
    have hend : 2 * Real.exp (-Real.log (2 / δ)) = δ := by
      rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 2 / δ)]
      field_simp
    exact htail.trans (by
      rw [hexp]
      calc
        _ ≤ 2 * Real.exp (-Real.log (2 / δ)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
        _ = δ := hend
        _ ≤ ε := hδε)
  · change (n : ℝ) ≤ 4 * |τ| + 8 * Real.log (8 / δ) + 8
    dsimp [a] at hnu
    linarith

end Qatlib.Concepts.SignalPrimitive.MainResults
