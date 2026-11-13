/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Trace norm bounded by rank and Hilbert–Schmidt norm

Proves `traceNorm_sq_le_rank_hilbertSchmidt` for a finite complex square matrix. Its squared
trace norm is at most its rank times the real trace of `A.conjTranspose * A`, equivalently its
rank times its squared Hilbert–Schmidt norm. See [Bhatia1997] for related background.

## Main statements

* `traceNorm_sq_le_rank_hilbertSchmidt`: The squared trace norm of a finite complex matrix is at
  most its rank times its squared Hilbert–Schmidt norm, expressed as `((A.conjTranspose *
  A).trace).re`.

## References

* [Bhatia, 1997][Bhatia1997]
-/

namespace Qatlib.Foundations.MixedFidelity.TraceNormRankBound

open scoped BigOperators ComplexOrder

set_option autoImplicit false

/-- The squared trace norm of a finite complex matrix is at most its rank times its squared
Hilbert–Schmidt norm, expressed as `((A.conjTranspose * A).trace).re`. -/
theorem traceNorm_sq_le_rank_hilbertSchmidt
    {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) :
    A.traceNorm ^ 2 ≤ (A.rank : ℝ) * ((A.conjTranspose * A).trace).re := by
  classical
  let hG : (A.conjTranspose * A).IsHermitian :=
    (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian
  let eigenvalue : I → ℝ := hG.eigenvalues
  let support : Finset I := Finset.univ.filter fun i => eigenvalue i ≠ 0
  have hnonneg (i : I) : 0 ≤ eigenvalue i := by
    simpa only [eigenvalue, Matrix.conjTranspose_conjTranspose] using
      Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i
  have hsingular (i : I) : singularValues A i = Real.sqrt (eigenvalue i) := by
    simp only [singularValues, Matrix.conjTranspose_conjTranspose, eigenvalue]
  have htrace : (∑ i : I, eigenvalue i) =
      ((A.conjTranspose * A).trace).re := by
    simpa only [eigenvalue, Complex.re_sum, Complex.ofReal_re] using!
      congrArg Complex.re hG.sum_eigenvalues_eq_trace
  have hcard : support.card = A.rank := by
    calc
      support.card = Fintype.card {i : I // eigenvalue i ≠ 0} := by
        simp [support, Fintype.card_subtype]
      _ = (A.conjTranspose * A).rank := by
        simpa only [eigenvalue] using hG.rank_eq_card_non_zero_eigs.symm
      _ = A.rank := Matrix.rank_conjTranspose_mul_self A
  have hsum : (∑ i ∈ support, Real.sqrt (eigenvalue i)) = A.traceNorm := by
    rw [Matrix.traceNorm_eq_sum_singularValues]
    simp_rw [hsingular]
    apply Finset.sum_subset (Finset.subset_univ support)
    intro i _ hnot
    have hz : eigenvalue i = 0 := by simpa [support] using hnot
    simp [hz]
  have hsquares : (∑ i ∈ support, Real.sqrt (eigenvalue i) ^ 2) =
      ((A.conjTranspose * A).trace).re := by
    calc
      (∑ i ∈ support, Real.sqrt (eigenvalue i) ^ 2) =
          ∑ i ∈ support, eigenvalue i := by
        apply Finset.sum_congr rfl
        intro i _
        exact Real.sq_sqrt (hnonneg i)
      _ = ∑ i : I, eigenvalue i := by
        apply Finset.sum_subset (Finset.subset_univ support)
        intro i _ hnot
        simpa [support] using hnot
      _ = ((A.conjTranspose * A).trace).re := htrace
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq support
    (fun _ : I => (1 : ℝ)) (fun i => Real.sqrt (eigenvalue i))
  simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one,
    hsum, hsquares, hcard] using hcauchy

end Qatlib.Foundations.MixedFidelity.TraceNormRankBound
