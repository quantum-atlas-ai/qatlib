/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

/-!
# Polynomial eigenvalue-transform robustness

For a fixed complex polynomial, polynomial evaluation is Lipschitz on
each bounded operator ball. On Hermitian contractions, polynomial
evaluation agrees with evaluating the polynomial on the eigenvalues, so
this gives a bound for the polynomial case of [GilyenSuLowWiebe2019],
Theorem 20 ([arXiv:1806.01838v1](https://arxiv.org/abs/1806.01838v1),
pp. 21–22). The constant depends on the polynomial and the radius and is
chosen before the two operators. The norms are the continuous operator
norm on Euclidean space and the matching matrix L2 operator norm.

The general modulus-of-continuity bound with a logarithmic factor
remains open in this formalization.
-/

set_option autoImplicit false

noncomputable section

open Polynomial
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.QSingValue19.QsVtStability

variable {Operator : Type*} [NormedRing Operator] [NormOneClass Operator]
  [NormedAlgebra ℂ Operator]

omit [NormedAlgebra ℂ Operator] in
/-- A uniform degree-and-radius bound for the difference of two powers in a
normed algebra.  The exponent is deliberately bounded by `(k + 1) * R ^ k`;
it is not presented as the source's sharp derivative estimate. -/
private theorem pow_sub_pow_norm_le {x y : Operator} {R : ℝ} (hR : 1 ≤ R)
    (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (k : ℕ) :
    ‖x ^ k - y ^ k‖ ≤ (((k : ℕ) + 1 : ℝ) * R ^ k) * ‖x - y‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsplit : x ^ (k + 1) - y ^ (k + 1) = x * (x ^ k - y ^ k) + (x - y) * y ^ k := by
      rw [pow_succ', pow_succ', mul_sub, sub_mul]
      abel
    have hRnonneg : 0 ≤ R := zero_le_one.trans hR
    have hyk : ‖y ^ k‖ ≤ R ^ k :=
      (norm_pow_le y k).trans (pow_le_pow_left₀ (norm_nonneg y) hy k)
    calc ‖x ^ (k + 1) - y ^ (k + 1)‖
        = ‖x * (x ^ k - y ^ k) + (x - y) * y ^ k‖ := by rw [hsplit]
      _ ≤ ‖x * (x ^ k - y ^ k)‖ + ‖(x - y) * y ^ k‖ := norm_add_le _ _
      _ ≤ R * ((((k : ℕ) + 1 : ℝ) * R ^ k) * ‖x - y‖)
          + ‖x - y‖ * R ^ k := by
          refine add_le_add ?_ ?_
          · calc ‖x * (x ^ k - y ^ k)‖
                ≤ ‖x‖ * ‖x ^ k - y ^ k‖ := norm_mul_le x (x ^ k - y ^ k)
              _ ≤ R * ((((k : ℕ) + 1 : ℝ) * R ^ k) * ‖x - y‖) :=
                  mul_le_mul hx ih (norm_nonneg _) hRnonneg
          · calc ‖(x - y) * y ^ k‖
                ≤ ‖x - y‖ * ‖y ^ k‖ := norm_mul_le (x - y) (y ^ k)
              _ ≤ ‖x - y‖ * R ^ k := mul_le_mul_of_nonneg_left hyk (norm_nonneg (x - y))
      _ ≤ ((((k + 1 : ℕ) : ℝ) + 1) * R ^ (k + 1)) * ‖x - y‖ := by
          have hextra : 0 ≤ (R - 1) * R ^ k * ‖x - y‖ :=
            mul_nonneg (mul_nonneg (sub_nonneg.mpr hR) (pow_nonneg hRnonneg k))
              (norm_nonneg _)
          have hcalc :
              ((((k + 1 : ℕ) : ℝ) + 1) * R ^ (k + 1)) * ‖x - y‖
                = R * ((((k : ℕ) + 1 : ℝ) * R ^ k) * ‖x - y‖)
                  + ‖x - y‖ * R ^ k + (R - 1) * R ^ k * ‖x - y‖ := by
            push_cast
            ring
          rw [hcalc]
          exact le_add_of_nonneg_right hextra

/-- The polynomial bound behind the restricted Theorem 20 increment. -/
private theorem polynomial_aeval_sub_norm_le (p : ℂ[X]) {x y : Operator} {R : ℝ}
    (hR : 1 ≤ R) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    ‖aeval x p - aeval y p‖ ≤
      (∑ i ∈ Finset.range (p.natDegree + 1),
        ‖p.coeff i‖ * (((i : ℕ) + 1 : ℝ) * R ^ i)) * ‖x - y‖ := by
  have hsum :
      (∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • x ^ i)
        - ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • y ^ i
      = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • (x ^ i - y ^ i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => (smul_sub (p.coeff i) (x ^ i) (y ^ i)).symm
  rw [aeval_eq_sum_range, aeval_eq_sum_range, hsum]
  calc ‖∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • (x ^ i - y ^ i)‖
      ≤ ∑ i ∈ Finset.range (p.natDegree + 1),
          ‖p.coeff i • (x ^ i - y ^ i)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1),
          ‖p.coeff i‖ * ((((i : ℕ) + 1 : ℝ) * R ^ i) * ‖x - y‖) := by
        refine Finset.sum_le_sum fun i _ => ?_
        calc ‖p.coeff i • (x ^ i - y ^ i)‖
            ≤ ‖p.coeff i‖ * ‖x ^ i - y ^ i‖ := norm_smul_le _ _
          _ ≤ ‖p.coeff i‖ * ((((i : ℕ) + 1 : ℝ) * R ^ i) * ‖x - y‖) :=
              mul_le_mul_of_nonneg_left
                (pow_sub_pow_norm_le hR hx hy i) (norm_nonneg _)
    _ = (∑ i ∈ Finset.range (p.natDegree + 1),
          ‖p.coeff i‖ * (((i : ℕ) + 1 : ℝ) * R ^ i)) * ‖x - y‖ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring

/-- Restricted Theorem 20 core: on operators of norm at most `R`, a fixed
complex polynomial transform has a Lipschitz constant independent of the two
operators.  The constant is fixed before `A` and `B` are introduced. -/
theorem theorem20PolynomialEigenvalueRobustness
    (n : Type*) [Fintype n] [Nonempty n] (p : ℂ[X]) {R : ℝ} (_hR : 1 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ A B : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n,
      ‖A‖ ≤ R → ‖B‖ ≤ R →
      ‖aeval A p - aeval B p‖ ≤ C * ‖A - B‖ := by
  refine ⟨1 + ∑ i ∈ Finset.range (p.natDegree + 1),
    ‖p.coeff i‖ * (((i : ℕ) + 1 : ℝ) * (max R 1) ^ i), ?_, ?_⟩
  · have hmax : 0 ≤ max R 1 := zero_le_one.trans (le_max_right R 1)
    have hsum : 0 ≤ ∑ i ∈ Finset.range (p.natDegree + 1),
        ‖p.coeff i‖ * (((i : ℕ) + 1 : ℝ) * (max R 1) ^ i) :=
      Finset.sum_nonneg fun i (_ : i ∈ Finset.range (p.natDegree + 1)) =>
      mul_nonneg (norm_nonneg (p.coeff i))
        (mul_nonneg (by positivity : (0 : ℝ) ≤ ((i : ℕ) + 1)) (pow_nonneg hmax i))
    linarith
  · intro A B hA hB
    have hR' : 1 ≤ max R 1 := le_max_right R 1
    have hA' : ‖A‖ ≤ max R 1 := le_max_of_le_left hA
    have hB' : ‖B‖ ≤ max R 1 := le_max_of_le_left hB
    have h := polynomial_aeval_sub_norm_le p hR' hA' hB'
    refine h.trans ?_
    have hmax : 0 ≤ max R 1 := zero_le_one.trans (le_max_right R 1)
    have hnonneg : 0 ≤ ∑ i ∈ Finset.range (p.natDegree + 1),
      ‖p.coeff i‖ * (((i : ℕ) + 1 : ℝ) * (max R 1) ^ i) :=
      Finset.sum_nonneg fun i (_ : i ∈ Finset.range (p.natDegree + 1)) =>
        mul_nonneg (norm_nonneg (p.coeff i))
          (mul_nonneg (by positivity : (0 : ℝ) ≤ ((i : ℕ) + 1)) (pow_nonneg hmax i))
    exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

/-- The same restricted Theorem 20 core stated directly for matrices.  The
matrix norm is the scoped L2 operator norm, hence agrees by definition
with the norm of the associated operator on Euclidean space. -/
theorem theorem20PolynomialEigenvalueRobustnessMatrix
    (n : Type*) [Fintype n] [DecidableEq n] [Nonempty n] (p : ℂ[X])
    {R : ℝ} (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ A B : Matrix n n ℂ,
      ‖A‖ ≤ R → ‖B‖ ≤ R →
      ‖aeval (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A) p -
        aeval (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) B) p‖
        ≤ C * ‖A - B‖ := by
  obtain ⟨C, hC, hbound⟩ :=
    theorem20PolynomialEigenvalueRobustness n p hR
  exact ⟨C, hC, fun A B hA hB => by
    have hA' : ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A‖ ≤ R := by
      rw [Matrix.l2_opNorm_toEuclideanCLM]
      exact hA
    have hB' : ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) B‖ ≤ R := by
      rw [Matrix.l2_opNorm_toEuclideanCLM]
      exact hB
    have hmap : Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A
        - Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) B
      = Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (A - B) := by
      simp
    have hbound' := hbound _ _ hA' hB'
    rw [hmap, Matrix.l2_opNorm_toEuclideanCLM] at hbound'
    exact hbound'⟩

end Qatlib.Papers.QSingValue19.QsVtStability
