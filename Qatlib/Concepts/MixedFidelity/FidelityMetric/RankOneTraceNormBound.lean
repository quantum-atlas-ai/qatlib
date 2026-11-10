/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MixedFidelity.TraceNormRankBound
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Real.Sqrt
set_option warningAsError false
open Qatlib.Foundations.MixedFidelity.TraceNormRankBound
open Qatlib

namespace Qatlib.Concepts.MixedFidelity.FidelityMetric

open scoped BigOperators

set_option autoImplicit false

private theorem rankOne_sum_star_self
    {I : Type*} [Fintype I] (u : I → ℂ) :
    (∑ i, star (u i) * u i) = ((∑ i, Complex.normSq (u i) : ℝ) : ℂ) := by
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [Complex.star_def] using
    (Complex.normSq_eq_conj_mul_self (z := u i)).symm

private theorem rankOne_outer_pair_trace
    {I : Type*} [Fintype I] (u v w : I → ℂ) :
    (Matrix.vecMulVec u (star v) * Matrix.vecMulVec w (star u)).trace =
      (∑ i, star (v i) * w i) * (∑ i, star (u i) * u i) := by
  rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.trace_vecMulVec]
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Pi.star_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem traceNorm_rankOne_le {I : Type*} [Fintype I] [DecidableEq I]
    (u v : I → ℂ) :
    (Matrix.vecMulVec u (star v)).traceNorm ≤
      Real.sqrt ((∑ i, Complex.normSq (u i)) * (∑ i, Complex.normSq (v i))) := by
  let A : Matrix I I ℂ := Matrix.vecMulVec u (star v)
  let uNormSq : ℝ := ∑ i, Complex.normSq (u i)
  let vNormSq : ℝ := ∑ i, Complex.normSq (v i)
  have hu_nonneg : 0 ≤ uNormSq :=
    Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (u i)
  have hv_nonneg : 0 ≤ vNormSq :=
    Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (v i)
  have hrank : (A.rank : ℝ) ≤ 1 := by
    exact_mod_cast Matrix.rank_vecMulVec_le u (star v)
  have hgram : ((A.conjTranspose * A).trace).re = uNormSq * vNormSq := by
    change ((Matrix.vecMulVec u (star v)).conjTranspose *
      Matrix.vecMulVec u (star v)).trace.re = uNormSq * vNormSq
    rw [Matrix.conjTranspose_vecMulVec, star_star, rankOne_outer_pair_trace,
      rankOne_sum_star_self, rankOne_sum_star_self]
    simp only [← Complex.ofReal_mul, Complex.ofReal_re, uNormSq, vNormSq]
  apply Real.le_sqrt_of_sq_le
  change A.traceNorm ^ 2 ≤ uNormSq * vNormSq
  calc
    A.traceNorm ^ 2 ≤ (A.rank : ℝ) * ((A.conjTranspose * A).trace).re :=
      traceNorm_sq_le_rank_hilbertSchmidt A
    _ = (A.rank : ℝ) * (uNormSq * vNormSq) := by rw [hgram]
    _ ≤ 1 * (uNormSq * vNormSq) :=
      mul_le_mul_of_nonneg_right hrank (mul_nonneg hu_nonneg hv_nonneg)
    _ = uNormSq * vNormSq := one_mul _

end Qatlib.Concepts.MixedFidelity.FidelityMetric
