/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CompressedQuery.CyclicRecord.PhaseQuery

/-!
# Entries of the uniform swap and recording matrix

This module computes the empty and labelled entries of `uniformSwap` and expands the entries of
`recording`. For phases with zero sum, the empty-to-empty recording entry vanishes and the
labelled block has an explicit diagonal term and a uniform correction.

The mathematical context is discussed in [MagniezZur2026].

## Main statements

* `swap_some_some`: The labelled block of the uniform swap.
* `recording_none_none`: Vanishing of the empty recording entry for zero-sum phases.
* `recording_some_some`: The explicit labelled recording entries for zero-sum phases.

## References

* [Magniez and Zur, 2026][MagniezZur2026]
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Concepts.CompressedQuery.CyclicRecord
variable {L : Type*} [Fintype L]

/-- The empty-to-empty entry of the uniform swap is zero. -/
theorem swap_none_none : uniformSwap (L := L) none none=0 := by
  rw [uniformSwap,swapVector_star]
  simp [Matrix.sub_apply,Matrix.vecMulVec_apply,swapVector]

/-- The uniform swap entry from a labelled state to the empty state equals `coefficient L`. -/
theorem swap_none_some (y : L) : uniformSwap (L := L) none (some y)=(coefficient L : ℂ) := by
  rw [uniformSwap,swapVector_star]
  simp [Matrix.sub_apply,Matrix.vecMulVec_apply,swapVector]

/-- The uniform swap entry from the empty state to a labelled state equals `coefficient L`. -/
theorem swap_some_none (y : L) : uniformSwap (L := L) (some y) none=(coefficient L : ℂ) := by
  rw [uniformSwap,swapVector_star]
  simp [Matrix.sub_apply,Matrix.vecMulVec_apply,swapVector]

/-- The labelled block of the uniform swap has entries δ(x, y) minus the square of `coefficient
L`. -/
theorem swap_some_some (x y : L) :
    uniformSwap (L := L) (some x) (some y)=(if x=y then 1 else 0)-(coefficient L : ℂ)^2 := by
  rw [uniformSwap,swapVector_star]
  simp [Matrix.sub_apply,Matrix.vecMulVec_apply,swapVector,Matrix.one_apply,pow_two]

/-- A recording matrix entry is the empty intermediate contribution plus the sum of
phase-weighted labelled intermediate contributions. -/
theorem recording_entry (phase : L → ℂ) (i j : Option L) :
    recording phase i j=uniformSwap i none*uniformSwap none j+
      ∑ k : L, uniformSwap i (some k)*phase k*uniformSwap (some k) j := by
  unfold recording
  rw [Matrix.mul_apply]
  simp_rw [phaseGate,Matrix.mul_diagonal]
  rw [Fintype.sum_option]
  simp only [mul_one]

/-- Expand the finite sum of `(δ(x, k) − a) * f k * (δ(k, y) − a)` into its diagonal term, two
linear corrections and the total-sum term. -/
theorem sum_delta_sub (f : L → ℂ) (a : ℂ) (x y : L) :
    (∑ k : L, ((if x=k then 1 else 0)-a)*f k*((if k=y then 1 else 0)-a))=
      (if x=y then f x else 0)-a*f x-a*f y+a^2*∑ k, f k := by
  simp_rw [sub_mul,mul_sub,ite_mul,mul_ite,one_mul,mul_one,zero_mul,mul_zero]
  simp only [ite_self,Finset.sum_sub_distrib,Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  simp only [← Finset.mul_sum,← Finset.sum_mul]
  ring

/-- If the phases sum to zero, the empty-to-empty recording matrix entry is zero. -/
theorem recording_none_none (phase : L → ℂ) (hzero : ∑ y,phase y=0) :
    recording phase none none=0 := by
  rw [recording_entry,swap_none_none]
  simp_rw [swap_none_some,swap_some_none]
  simp only [zero_mul,zero_add,← Finset.sum_mul,← Finset.mul_sum,hzero,mul_zero,zero_mul]

/-- If the phases sum to zero, the labelled recording entry is `δ(x, y) * phase x` plus
`coefficient L` squared times `1 − phase x − phase y`. -/
theorem recording_some_some (phase : L → ℂ) (hzero : ∑ y,phase y=0) (x y : L) :
    recording phase (some x) (some y)=
      (if x=y then phase x else 0)+(coefficient L : ℂ)^2*(1-phase x-phase y) := by
  rw [recording_entry,swap_some_none,swap_none_some]
  simp_rw [swap_some_some]
  rw [sum_delta_sub,hzero]
  ring
end Qatlib.Concepts.CompressedQuery.CyclicRecord
