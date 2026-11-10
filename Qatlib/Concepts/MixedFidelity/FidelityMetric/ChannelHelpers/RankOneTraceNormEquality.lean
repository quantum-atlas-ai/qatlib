/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedFidelity.FidelityMetric.RankOneTraceNormBound
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Concepts.MixedFidelity.FidelityMetric
open scoped BigOperators ComplexOrder

theorem hilbertSchmidt_le_traceNorm_sq
    {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) :
    ((A.conjTranspose * A).trace).re ≤ A.traceNorm ^ 2 := by
  let hG := (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian
  have hn (i : I) : 0 ≤ hG.eigenvalues i := by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i
  have hs (i : I) : singularValues A i = Real.sqrt (hG.eigenvalues i) := by
    simp only [singularValues, Matrix.conjTranspose_conjTranspose]
  have ht : (∑ i : I, hG.eigenvalues i) = ((A.conjTranspose * A).trace).re := by
    simpa only [Complex.re_sum, Complex.ofReal_re] using!
      congrArg Complex.re hG.sum_eigenvalues_eq_trace
  have hsq : (∑ i : I, singularValues A i ^ 2) = ((A.conjTranspose * A).trace).re := by
    simp_rw [hs, Real.sq_sqrt (hn _)]
    exact ht
  rw [← hsq, Matrix.traceNorm_eq_sum_singularValues]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => singularValues_nonneg A i)

private theorem rankOne_gram_trace {I : Type*} [Fintype I]
    (u v : I → ℂ) :
    (((Matrix.vecMulVec u (star v)).conjTranspose *
      Matrix.vecMulVec u (star v)).trace).re =
      (∑ i, Complex.normSq (u i)) * (∑ i, Complex.normSq (v i)) := by
  have hsum (w : I → ℂ) : (∑ i, star (w i) * w i) =
      ((∑ i, Complex.normSq (w i) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [Complex.star_def] using (Complex.normSq_eq_conj_mul_self (z := w i)).symm
  rw [Matrix.conjTranspose_vecMulVec, star_star, Matrix.vecMulVec_mul_vecMulVec,
    Matrix.trace_vecMulVec]
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Pi.star_apply]
  have hfactor : (∑ i : I, v i * ((∑ j : I, star (u j) * u j) * star (v i))) =
      (∑ j : I, star (u j) * u j) * (∑ i : I, star (v i) * v i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hfactor, hsum, hsum]
  simp only [← Complex.ofReal_mul, Complex.ofReal_re]

theorem traceNorm_rankOne_eq {I : Type*} [Fintype I] [DecidableEq I]
    (u v : I → ℂ) :
    (Matrix.vecMulVec u (star v)).traceNorm =
      Real.sqrt ((∑ i, Complex.normSq (u i)) * (∑ i, Complex.normSq (v i))) := by
  apply le_antisymm (Qatlib.Concepts.MixedFidelity.FidelityMetric.traceNorm_rankOne_le u v)
  apply (Real.sqrt_le_iff).2
  exact ⟨Matrix.traceNorm_nonneg _, by
    rw [← rankOne_gram_trace u v]
    exact Qatlib.Concepts.MixedFidelity.FidelityMetric.hilbertSchmidt_le_traceNorm_sq _⟩

private theorem finite_sum_traceNorm_le {I X : Type*} [Fintype I] [DecidableEq I]
    (s : Finset X) (A : X → Matrix I I ℂ) :
    (∑ x ∈ s, A x).traceNorm ≤ ∑ x ∈ s, (A x).traceNorm := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
    simp only [Finset.sum_insert hx]
    exact (Matrix.traceNorm_add_le _ _).trans (add_le_add_right ih _)

theorem traceNorm_weighted_sum_le {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (A : X → Matrix I I ℂ) :
    (∑ x, (p x : ℂ) • A x).traceNorm ≤ ∑ x, p x * (A x).traceNorm := by
  simpa only [Matrix.traceNorm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hp _)] using finite_sum_traceNorm_le Finset.univ (fun x => (p x : ℂ) • A x)

theorem traceNorm_probability_sum_le {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hone : ∑ x, p x = 1)
    (A : X → Matrix I I ℂ) (R : ℝ) (hR : ∀ x, (A x).traceNorm ≤ R) :
    (∑ x, (p x : ℂ) • A x).traceNorm ≤ R := by
  calc
    _ ≤ ∑ x, p x * (A x).traceNorm := Qatlib.Concepts.MixedFidelity.FidelityMetric.traceNorm_weighted_sum_le p hp A
    _ ≤ ∑ x, p x * R := Finset.sum_le_sum fun x _ =>
      mul_le_mul_of_nonneg_left (hR x) (hp x)
    _ = R := by rw [← Finset.sum_mul, hone, one_mul]

end Qatlib.Concepts.MixedFidelity.FidelityMetric
