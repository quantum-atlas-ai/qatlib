/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MatProdVerify04.MainResults

open Finset

theorem inv_sqrt_le_two_diff {j : ℕ} (hj : 0 < j) :
    1 / Real.sqrt (j : ℝ) ≤ 2 * (Real.sqrt (j : ℝ) - Real.sqrt ((j - 1 : ℕ) : ℝ)) := by
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hpredR : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : (1 : ℕ) ≤ j)]
    norm_num
  have hpred0 : (0 : ℝ) ≤ ((j - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsj : 0 < Real.sqrt (j : ℝ) := Real.sqrt_pos.mpr hjR
  have hsp : 0 ≤ Real.sqrt ((j - 1 : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hsum : 0 < Real.sqrt (j : ℝ) + Real.sqrt ((j - 1 : ℕ) : ℝ) := by positivity

  have hdiff : Real.sqrt (j : ℝ) - Real.sqrt ((j - 1 : ℕ) : ℝ)
      = 1 / (Real.sqrt (j : ℝ) + Real.sqrt ((j - 1 : ℕ) : ℝ)) := by
    rw [eq_div_iff hsum.ne']
    have hsj2 : (Real.sqrt (j : ℝ)) ^ 2 = (j : ℝ) := Real.sq_sqrt hjR.le
    have hsp2 : (Real.sqrt ((j - 1 : ℕ) : ℝ)) ^ 2 = ((j - 1 : ℕ) : ℝ) :=
      Real.sq_sqrt hpred0
    nlinarith [hsj2, hsp2, hpredR]
  rw [hdiff, mul_one_div]
  rw [div_le_iff₀ hsj, div_mul_eq_mul_div, le_div_iff₀ hsum]
  have hspj : Real.sqrt ((j - 1 : ℕ) : ℝ) ≤ Real.sqrt (j : ℝ) := by
    apply Real.sqrt_le_sqrt
    rw [hpredR]
    linarith
  linarith

theorem grover_sum_le (r : ℕ) :
    (∑ i ∈ Finset.range r, 1 / Real.sqrt ((i : ℝ) + 1)) ≤ 2 * Real.sqrt (r : ℝ) := by
  have hterm : ∀ i ∈ Finset.range r,
      1 / Real.sqrt ((i : ℝ) + 1)
        ≤ 2 * (Real.sqrt ((i : ℝ) + 1) - Real.sqrt (i : ℝ)) := by
    intro i _
    have h := inv_sqrt_le_two_diff (j := i + 1) (by omega)
    simpa [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] using h
  calc (∑ i ∈ Finset.range r, 1 / Real.sqrt ((i : ℝ) + 1))
      ≤ ∑ i ∈ Finset.range r,
          2 * (Real.sqrt ((i : ℝ) + 1) - Real.sqrt (i : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = 2 * ∑ i ∈ Finset.range r, (Real.sqrt ((i : ℝ) + 1) - Real.sqrt (i : ℝ)) := by
        rw [Finset.mul_sum]
    _ = 2 * (Real.sqrt (r : ℝ) - Real.sqrt (0 : ℝ)) := by
        congr 1
        simpa using Finset.sum_range_sub (fun i : ℕ => Real.sqrt (i : ℝ)) r
    _ = 2 * Real.sqrt (r : ℝ) := by simp

theorem grover_row_time {n m : ℝ} (hn : 0 ≤ n) (hm : 0 ≤ m) (r : ℕ) :
    (∑ i ∈ Finset.range r, Real.sqrt (n / ((i : ℝ) + 1)) * m)
      ≤ 2 * Real.sqrt (n * r) * m := by
  calc (∑ i ∈ Finset.range r, Real.sqrt (n / ((i : ℝ) + 1)) * m)
      = (∑ i ∈ Finset.range r, Real.sqrt (n / ((i : ℝ) + 1))) * m := by
        rw [Finset.sum_mul]
    _ = (∑ i ∈ Finset.range r, Real.sqrt n / Real.sqrt ((i : ℝ) + 1)) * m := by
        congr 1
        exact Finset.sum_congr rfl (fun i _ => by
          rw [Real.sqrt_div hn])
    _ = (Real.sqrt n * ∑ i ∈ Finset.range r, 1 / Real.sqrt ((i : ℝ) + 1)) * m := by
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
    _ ≤ (Real.sqrt n * (2 * Real.sqrt (r : ℝ))) * m := by
        have hs := grover_sum_le r
        have hsn : 0 ≤ Real.sqrt n := Real.sqrt_nonneg n
        have : Real.sqrt n * (∑ i ∈ Finset.range r, 1 / Real.sqrt ((i : ℝ) + 1))
            ≤ Real.sqrt n * (2 * Real.sqrt (r : ℝ)) :=
          mul_le_mul_of_nonneg_left hs hsn
        exact mul_le_mul_of_nonneg_right this hm
    _ = 2 * Real.sqrt (n * r) * m := by
        rw [Real.sqrt_mul hn]
        ring

theorem sum_sqrt_le_sqrt_mul_sum {r : ℕ} {f : ℕ → ℝ} (hf : ∀ i, 0 ≤ f i) :
    (∑ i ∈ Finset.range r, Real.sqrt (f i))
      ≤ Real.sqrt ((r : ℝ) * ∑ i ∈ Finset.range r, f i) := by
  have hsq : (∑ i ∈ Finset.range r, Real.sqrt (f i)) ^ 2
      ≤ (r : ℝ) * ∑ i ∈ Finset.range r, f i := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range r)
      (fun _ => (1 : ℝ)) (fun i => Real.sqrt (f i))
    simpa [Real.sq_sqrt (hf _), Finset.sum_const, nsmul_eq_mul] using h
  have hnn : 0 ≤ ∑ i ∈ Finset.range r, Real.sqrt (f i) :=
    Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)
  calc (∑ i ∈ Finset.range r, Real.sqrt (f i))
      = Real.sqrt ((∑ i ∈ Finset.range r, Real.sqrt (f i)) ^ 2) :=
        (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt ((r : ℝ) * ∑ i ∈ Finset.range r, f i) := Real.sqrt_le_sqrt hsq

end Qatlib.Papers.MatProdVerify04.MainResults
