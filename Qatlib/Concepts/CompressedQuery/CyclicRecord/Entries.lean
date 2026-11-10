/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CompressedQuery.CyclicRecord.PhaseQuery

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Concepts.CompressedQuery.CyclicRecord
variable {L : Type*} [Fintype L]

theorem swap_none_none : uniformSwap (L := L) none none=0 := by
  rw [uniformSwap,swapVector_star]
  simp [Matrix.sub_apply,Matrix.vecMulVec_apply,swapVector]

theorem swap_none_some (y : L) : uniformSwap (L := L) none (some y)=(coefficient L : ℂ) := by
  rw [uniformSwap,swapVector_star]
  simp [Matrix.sub_apply,Matrix.vecMulVec_apply,swapVector]

theorem swap_some_none (y : L) : uniformSwap (L := L) (some y) none=(coefficient L : ℂ) := by
  rw [uniformSwap,swapVector_star]
  simp [Matrix.sub_apply,Matrix.vecMulVec_apply,swapVector]

theorem swap_some_some (x y : L) :
    uniformSwap (L := L) (some x) (some y)=(if x=y then 1 else 0)-(coefficient L : ℂ)^2 := by
  rw [uniformSwap,swapVector_star]
  simp [Matrix.sub_apply,Matrix.vecMulVec_apply,swapVector,Matrix.one_apply,pow_two]

theorem recording_entry (phase : L → ℂ) (i j : Option L) :
    recording phase i j=uniformSwap i none*uniformSwap none j+
      ∑ k : L, uniformSwap i (some k)*phase k*uniformSwap (some k) j := by
  unfold recording
  rw [Matrix.mul_apply]
  simp_rw [phaseGate,Matrix.mul_diagonal]
  rw [Fintype.sum_option]
  simp only [mul_one]

theorem sum_delta_sub (f : L → ℂ) (a : ℂ) (x y : L) :
    (∑ k : L, ((if x=k then 1 else 0)-a)*f k*((if k=y then 1 else 0)-a))=
      (if x=y then f x else 0)-a*f x-a*f y+a^2*∑ k, f k := by
  simp_rw [sub_mul,mul_sub,ite_mul,mul_ite,one_mul,mul_one,zero_mul,mul_zero]
  simp only [ite_self,Finset.sum_sub_distrib,Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  simp only [← Finset.mul_sum,← Finset.sum_mul]
  ring

theorem recording_none_none (phase : L → ℂ) (hzero : ∑ y,phase y=0) :
    recording phase none none=0 := by
  rw [recording_entry,swap_none_none]
  simp_rw [swap_none_some,swap_some_none]
  simp only [zero_mul,zero_add,← Finset.sum_mul,← Finset.mul_sum,hzero,mul_zero,zero_mul]

theorem recording_some_some (phase : L → ℂ) (hzero : ∑ y,phase y=0) (x y : L) :
    recording phase (some x) (some y)=
      (if x=y then phase x else 0)+(coefficient L : ℂ)^2*(1-phase x-phase y) := by
  rw [recording_entry,swap_some_none,swap_none_some]
  simp_rw [swap_some_some]
  rw [sum_delta_sub,hzero]
  ring
end Qatlib.Concepts.CompressedQuery.CyclicRecord
