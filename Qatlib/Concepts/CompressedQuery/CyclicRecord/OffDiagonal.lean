/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CompressedQuery.CyclicRecord.Entries

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Concepts.CompressedQuery.CyclicRecord
variable {L : Type*} [Fintype L]

theorem recording_none_some (phase : L → ℂ) (hzero : ∑ y,phase y=0) (y : L) :
    recording phase none (some y)=(coefficient L : ℂ)*phase y := by
  rw [recording_entry,swap_none_none]
  simp_rw [swap_none_some,swap_some_some,mul_sub,mul_ite,mul_one,mul_zero]
  simp only [zero_mul,zero_add,Finset.sum_sub_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  simp only [← Finset.sum_mul,← Finset.mul_sum,hzero,mul_zero,zero_mul,sub_zero]

theorem recording_some_none (phase : L → ℂ) (hzero : ∑ y,phase y=0) (x : L) :
    recording phase (some x) none=(coefficient L : ℂ)*phase x := by
  rw [recording_entry,swap_none_none]
  simp_rw [swap_some_none,swap_some_some,sub_mul,ite_mul,one_mul,zero_mul]
  simp only [mul_zero,zero_add,Finset.sum_sub_distrib,Finset.sum_ite_eq,Finset.mem_univ,if_true]
  simp only [← Finset.sum_mul,← Finset.mul_sum,hzero,mul_zero,zero_mul,sub_zero]
  ring

theorem coefficient_nonneg : 0 ≤ coefficient L := by unfold coefficient;positivity

theorem coefficient_sq : coefficient L^2=1/(Fintype.card L : ℝ) := by
  simp only [coefficient,div_pow,one_pow,Real.sq_sqrt (Nat.cast_nonneg _)]

theorem recording_off_diagonal_bound (phase : L → ℂ) (hzero : ∑ y,phase y=0)
    (hp : ∀ y, ‖phase y‖=1) (x y : L) (hxy : x ≠ y) :
    ‖recording phase (some x) (some y)‖ ≤ 3/(Fintype.card L : ℝ) := by
  rw [recording_some_some phase hzero x y,if_neg hxy,zero_add,norm_mul,norm_pow]
  have hn : ‖(coefficient L : ℂ)‖=coefficient L := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg coefficient_nonneg]
  rw [hn]
  have ha := norm_sub_le (1 : ℂ) (phase x)
  have hb := norm_sub_le (1-phase x) (phase y)
  rw [norm_one,hp x] at ha
  rw [hp y] at hb
  have hc : ‖1-phase x-phase y‖ ≤ 3 := by linarith
  calc
    _ ≤ coefficient L^2*3 := mul_le_mul_of_nonneg_left hc (sq_nonneg _)
    _ = _ := by rw [coefficient_sq];ring
end Qatlib.Concepts.CompressedQuery.CyclicRecord
