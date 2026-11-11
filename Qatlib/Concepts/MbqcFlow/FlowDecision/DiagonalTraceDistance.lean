/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MixedFidelity.TraceNormRankBound

/-!
# Diagonal entries controlled by trace distance

This module proves `abs_diagonal_re_le_half_traceNorm`: each real diagonal entry of a finite
Hermitian matrix with trace zero has absolute value at most half its trace norm. Applied to a
difference of density operators, this controls differences of computational-basis measurement
probabilities by trace distance, as in the distinguishability framework of [Watrous2018].

## Main statements

* `abs_diagonal_re_le_half_traceNorm`: the diagonal-entry bound for a trace-zero Hermitian
  matrix.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

open scoped BigOperators

/-- For a finite Hermitian matrix with trace zero, the absolute real part of any diagonal entry
is at most half its trace norm. -/
theorem abs_diagonal_re_le_half_traceNorm
    {I : Type*} [Fintype I] [DecidableEq I] (X : Matrix I I ℂ)
    (_hX : X.IsHermitian) (htrace : X.trace = 0) (i : I) :
    |(X i i).re| ≤ (1 / 2 : ℝ) * X.traceNorm := by
  classical
  let U : Matrix I I ℂ := Matrix.diagonal (fun j => if j = i then 1 else -1)
  have hu : U.Isometry := by
    change U.conjTranspose * U = 1
    simp only [U, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    ext j k
    by_cases h : j = k
    · subst k
      by_cases hji : j = i <;> simp [hji]
    · simp [Matrix.diagonal, h]
  have ht : (U * X).trace = 2 * X i i := by
    have he (j : I) : (if j = i then (1 : ℂ) else -1) * X j j =
        2 * (if j = i then X i i else 0) - X j j := by
      by_cases h : j = i
      · rw [if_pos h]
        subst j
        simp only [ite_true]
        ring
      · simp [h]
    change (∑ j, (U * X) j j) = _
    simp only [U, Matrix.diagonal_mul, he, Finset.sum_sub_distrib,
      ← Finset.mul_sum]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ i)]
    change 2 * X i i - X.trace = _
    rw [htrace, sub_zero]
  have hb := Matrix.abs_trace_le_traceNorm (U * X)
  rw [Matrix.traceNorm_isometry_left (by convert! hu using 1), ht, norm_mul] at hb
  have hr := Complex.abs_re_le_norm (X i i)
  norm_num at hb
  linarith

end Qatlib.Concepts.MbqcFlow.FlowDecision
