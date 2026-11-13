/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# A finite measurement optimality criterion

This module proves a finite-dimensional trace criterion for optimality of a measurement, as used
in the quantum matching analysis of [SasakiCarlini2002]. Auxiliary results express products of
rank-one effects and prove that the real trace of a product of positive semidefinite matrices is
nonnegative.

The theorem `helstromYuen_optimality` compares any competing positive complete family with the
given family when its associated matrix `Γ` dominates every score matrix.

## Main statements

* `trace_mul_nonneg`: nonnegativity of the real trace of a product of positive semidefinite
  matrices.
* `helstromYuen_optimality`: a dominance certificate bounds every competing measurement score.

## References

* [Sasaki and Carlini, 2002][SasakiCarlini2002]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.QMatching02.MainResults.OptimalityCriterion

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in

/-- The trace of the product of two conjugate outer products is the product of their two
conjugated overlaps. -/
theorem trace_vecMulVec_mul_vecMulVec (a b : n → ℂ) :
    ((vecMulVec a (star a)) * (vecMulVec b (star b))).trace
      = (star a ⬝ᵥ b) * (star b ⬝ᵥ a) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.vecMulVec_apply,
    dotProduct]
  rw [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

omit [DecidableEq n] in

/-- The conjugated dot product of `x` with `y` is the complex conjugate of the conjugated dot
product of `y` with `x`. -/
theorem dotProduct_star_comm (x y : n → ℂ) :
    (star x ⬝ᵥ y) = star (star y ⬝ᵥ x) := by
  simp only [dotProduct, star_sum]
  apply Finset.sum_congr rfl; intro i _
  simp [mul_comm]

/-- The real part of the trace of a product of two positive semidefinite complex matrices is
nonnegative. -/
theorem trace_mul_nonneg {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ Complex.re ((A * B).trace) := by
  let _ := (inferInstance : DecidableEq n)
  obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hA
  obtain ⟨p, w, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hB
  rw [Finset.sum_mul_sum]
  simp only [Matrix.trace_sum, Complex.re_sum]
  apply Finset.sum_nonneg; intro i _
  apply Finset.sum_nonneg; intro j _
  rw [trace_vecMulVec_mul_vecMulVec, dotProduct_star_comm (w j) (v i)]
  have hz : Complex.re ((star (v i) ⬝ᵥ w j) * star (star (v i) ⬝ᵥ w j))
      = Complex.normSq (star (v i) ⬝ᵥ w j) := by
    simp [Complex.mul_conj, Complex.ofReal_re]
  rw [hz]
  exact Complex.normSq_nonneg _

/-- If a positive complete family `μ` has `Γ = ∑ i, μ i * G i` and `Γ - G i` positive
semidefinite for every `i`, then its real trace score bounds that of every positive complete
family `ν`. -/
theorem helstromYuen_optimality
    {ι : Type*} [Fintype ι]
    (G μ : ι → Matrix n n ℂ) (Γ : Matrix n n ℂ)
    (_hμ : ∀ i, (μ i).PosSemidef) (_hμsum : (∑ i, μ i) = 1)
    (hΓ : Γ = ∑ i, μ i * G i)
    (hDom : ∀ i, (Γ - G i).PosSemidef) :
    ∀ ν : ι → Matrix n n ℂ, (∀ i, (ν i).PosSemidef) → (∑ i, ν i) = 1 →
      (∑ i, Complex.re (((ν i) * G i).trace)) ≤ (∑ i, Complex.re (((μ i) * G i).trace)) := by
  intro ν hν hνsum

  have hstep : ∀ i ∈ (Finset.univ : Finset ι),
      Complex.re (((ν i) * G i).trace) ≤ Complex.re (((ν i) * Γ).trace) := by
    intro i _
    have hpsd := trace_mul_nonneg (hν i) (hDom i)
    have hsub : (ν i) * (Γ - G i) = (ν i) * Γ - (ν i) * G i := by
      rw [Matrix.mul_sub]
    rw [hsub, Matrix.trace_sub, Complex.sub_re] at hpsd
    linarith
  refine le_trans (Finset.sum_le_sum hstep) ?_

  have hmid : (∑ i, Complex.re (((ν i) * Γ).trace)) = Complex.re Γ.trace := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, hνsum, one_mul]
  rw [hmid, hΓ, Matrix.trace_sum, Complex.re_sum]

end Qatlib.Papers.QMatching02.MainResults.OptimalityCriterion
