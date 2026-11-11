/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedFidelity.FidelityMetric.ChannelHelpers.RankOneTraceNormEquality

/-!
# Trace-norm estimates for finite ensembles

`equation_one` gives the product-of-vector-norms formula for a rank-one matrix.
`lemma_three_three` bounds the trace norm of a finite ensemble by its average norm and then its
largest norm, while `lemma_three_three_distance_bound` applies the same convexity estimate to
differences of ensembles. See [Bhatia1997].

## Main statements

* `equation_one`: the rank-one trace norm.
* `lemma_three_three`: average and maximum trace-norm bounds.
* `lemma_three_three_distance_bound`: preservation of a common distance bound under mixing.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Concepts.MixedFidelity.FidelityMetric.FourierLabelHelpers
open scoped BigOperators

/-- The trace norm of `u vᴴ` equals the product of the square roots of the vectors' sums of
squared moduli. -/
theorem equation_one {I : Type*} [Fintype I] [DecidableEq I] (u v : I → ℂ) :
    (Matrix.vecMulVec u (star v)).traceNorm =
      Real.sqrt (∑ i, Complex.normSq (u i)) * Real.sqrt (∑ i, Complex.normSq (v i)) := by
  rw [Qatlib.Concepts.MixedFidelity.FidelityMetric.traceNorm_rankOne_eq, Real.sqrt_mul
    (Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg (u i)))]

/-- For a probability distribution on a nonempty finite index set, the trace norm of the matrix
average is at most the average trace norm, which is at most the largest trace norm. -/
theorem lemma_three_three {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [Nonempty X] (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hone : ∑ x, p x = 1) (A : X → Matrix I I ℂ) :
    (∑ x, (p x : ℂ) • A x).traceNorm ≤ ∑ x, p x * (A x).traceNorm ∧
      (∑ x, p x * (A x).traceNorm) ≤
        Finset.univ.sup' Finset.univ_nonempty (fun x => (A x).traceNorm) := by
  classical
  refine ⟨Qatlib.Concepts.MixedFidelity.FidelityMetric.traceNorm_weighted_sum_le p hp A, ?_⟩
  let R := Finset.univ.sup' Finset.univ_nonempty (fun x => (A x).traceNorm)
  calc
    _ ≤ ∑ x, p x * R := Finset.sum_le_sum fun x _ =>
      mul_le_mul_of_nonneg_left
        (Finset.le_sup' (fun x => (A x).traceNorm) (Finset.mem_univ x)) (hp x)
    _ = R := by rw [← Finset.sum_mul, hone, one_mul]

/-- If each pair of matrices has half trace-norm distance at most `R`, their averages with the
same probability weights also have half trace-norm distance at most `R`. -/
theorem lemma_three_three_distance_bound {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hone : ∑ x, p x = 1)
    (ρ σ : X → Matrix I I ℂ) (R : ℝ)
    (hR : ∀ x, (ρ x - σ x).traceNorm / 2 ≤ R) :
    ((∑ x, (p x : ℂ) • ρ x) - (∑ x, (p x : ℂ) • σ x)).traceNorm / 2 ≤ R := by
  have h := Qatlib.Concepts.MixedFidelity.FidelityMetric.traceNorm_probability_sum_le p hp hone
    (fun x => ρ x - σ x) (2 * R) (fun x => by linarith [hR x])
  simp only [smul_sub, Finset.sum_sub_distrib] at h
  linarith

end Qatlib.Concepts.MixedFidelity.FidelityMetric.FourierLabelHelpers
