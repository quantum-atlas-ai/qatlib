/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DecisionTrees97.MainResults.FiniteGraphPassage

/-!
# Mass conservation for the classical graph kernel

This module proves entry formulas, symmetry, and vanishing row and column sums for finite graph
Laplacians. It then establishes the derivative, semigroup law, and column-mass conservation of
the matrix exponential defining the classical kernel.

These constructions accompany the results of [FarhiGutmann1998].

## Main statements

* `sourceKernel_hasDerivAt`: identifies the derivative of the exponential kernel.
* `sourceKernel_column_sum_one`: proves conservation of complex column sums.
* `sourceClassicalKernel_mass_one`: proves that each real column sum is one.

## References

* [Farhi and Gutmann, 1998][FarhiGutmann1998]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.DecisionTrees97.MainResults

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

local instance : NormedAlgebra ℚ (Matrix V V ℂ) :=
  NormedAlgebra.restrictScalars ℚ ℂ (Matrix V V ℂ)

/-- The real graph Laplacian has vertex degrees on the diagonal, minus one on adjacent
off-diagonal entries, and zero elsewhere. See [FarhiGutmann1998]. -/
theorem lapMatrix_real_entries (i j : V) :
    G.lapMatrix ℝ i j =
      if i = j then (G.degree i : ℝ) else if G.Adj i j then -1 else 0 := by
  simp only [SimpleGraph.lapMatrix, Matrix.sub_apply, SimpleGraph.degMatrix,
    SimpleGraph.adjMatrix_apply]
  by_cases h : i = j
  · subst h
    simp
  · by_cases he : G.Adj i j <;> simp [h, he]

/-- The real graph Laplacian is symmetric entrywise. -/
theorem lapMatrix_symmetric (i j : V) :
    G.lapMatrix ℝ i j = G.lapMatrix ℝ j i := by
  have h : (G.lapMatrix ℝ)ᵀ = G.lapMatrix ℝ := SimpleGraph.isSymm_lapMatrix ℝ G
  exact congrFun (congrFun h.symm i) j

/-- Each row of the real graph Laplacian sums to zero. -/
theorem lapMatrix_real_row_sum_zero (i : V) :
    ∑ j : V, G.lapMatrix ℝ i j = 0 := by
  have h := congrFun (G.lapMatrix_mulVec_one_eq_zero ℝ) i
  simpa [Matrix.mulVec, dotProduct] using h

/-- Each column of the real graph Laplacian sums to zero. -/
theorem lapMatrix_real_col_sum_zero (j : V) :
    ∑ i : V, G.lapMatrix ℝ i j = 0 := by
  calc ∑ i : V, G.lapMatrix ℝ i j = ∑ i : V, G.lapMatrix ℝ j i :=
        Finset.sum_congr rfl fun i _ => lapMatrix_symmetric G i j
    _ = 0 := lapMatrix_real_row_sum_zero G j

/-- The complex graph Laplacian is symmetric entrywise. -/
theorem lapMatrix_complex_symmetric (i j : V) :
    G.lapMatrix ℂ i j = G.lapMatrix ℂ j i := by
  have h : (G.lapMatrix ℂ)ᵀ = G.lapMatrix ℂ := SimpleGraph.isSymm_lapMatrix ℂ G
  exact congrFun (congrFun h.symm i) j

/-- Each row of the complex graph Laplacian sums to zero. -/
theorem lapMatrix_complex_row_sum_zero (i : V) :
    ∑ j : V, G.lapMatrix ℂ i j = 0 := by
  have h := congrFun (G.lapMatrix_mulVec_one_eq_zero ℂ) i
  simpa [Matrix.mulVec, dotProduct] using h

/-- Each column of the complex graph Laplacian sums to zero. See [FarhiGutmann1998]. -/
theorem lapMatrix_complex_col_sum_zero (j : V) :
    ∑ i : V, G.lapMatrix ℂ i j = 0 := by
  calc ∑ i : V, G.lapMatrix ℂ i j = ∑ i : V, G.lapMatrix ℂ j i :=
        Finset.sum_congr rfl fun i _ => lapMatrix_complex_symmetric G i j
    _ = 0 := lapMatrix_complex_row_sum_zero G j

/-- The derivative of the graph heat kernel at `t` is minus the graph Laplacian multiplied by
the kernel at `t`. See [FarhiGutmann1998]. -/
theorem sourceKernel_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp ((-s : ℝ) • G.lapMatrix ℂ))
      ((-G.lapMatrix ℂ) * NormedSpace.exp ((-t : ℝ) • G.lapMatrix ℂ)) t := by
  letI : NormedAlgebra ℝ (Matrix V V ℂ) := NormedAlgebra.restrictScalars ℝ ℂ _
  simpa only [smul_neg, neg_smul] using
    (hasDerivAt_exp_smul_const' (-G.lapMatrix ℂ) t)

/-- The graph heat kernel at time zero is the identity matrix. -/
theorem sourceKernel_zero :
    NormedSpace.exp ((-(0 : ℝ)) • G.lapMatrix ℂ) = (1 : Matrix V V ℂ) := by
  simp

/-- The graph heat kernel at a sum of times is the product of the kernels at those times. See
[FarhiGutmann1998]. -/
theorem sourceKernel_add (s t : ℝ) :
    NormedSpace.exp ((-(s + t) : ℝ) • G.lapMatrix ℂ) =
      NormedSpace.exp ((-s : ℝ) • G.lapMatrix ℂ) *
        NormedSpace.exp ((-t : ℝ) • G.lapMatrix ℂ) := by
  have hcomm : Commute ((-s : ℝ) • G.lapMatrix ℂ) ((-t : ℝ) • G.lapMatrix ℂ) :=
    ((Commute.refl (G.lapMatrix ℂ)).smul_left (-s)).smul_right (-t)
  have h1 : NormedSpace.exp ((-s : ℝ) • G.lapMatrix ℂ) *
      NormedSpace.exp ((-t : ℝ) • G.lapMatrix ℂ) =
        NormedSpace.exp ((-s : ℝ) • G.lapMatrix ℂ + (-t : ℝ) • G.lapMatrix ℂ) :=
    (NormedSpace.exp_add_of_commute hcomm).symm
  rw [h1]
  congr 1
  rw [← add_smul, show (-(s + t) : ℝ) = -s + -t by ring]

/-- Every column of the complex graph heat kernel sums to one at every real time. See
[FarhiGutmann1998]. -/
theorem sourceKernel_column_sum_one (t : ℝ) (a : V) :
    ∑ b : V, NormedSpace.exp ((-t : ℝ) • G.lapMatrix ℂ) b a = 1 := by
  letI : NormedAlgebra ℝ (Matrix V V ℂ) := NormedAlgebra.restrictScalars ℝ ℂ _
  set A : Matrix V V ℂ := -G.lapMatrix ℂ with hA
  have hcol : ∀ c : V, ∑ b : V, A b c = 0 := by
    intro c
    have h := lapMatrix_complex_col_sum_zero G c
    simp only [hA, Matrix.neg_apply]
    rw [Finset.sum_neg_distrib, h, neg_zero]
  have hentry : ∀ (b : V) (s : ℝ), HasDerivAt (fun u : ℝ =>
      NormedSpace.exp (u • A) b a) ((A * NormedSpace.exp (s • A)) b a) s := by
    intro b s
    have hb : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • A))
        (A * NormedSpace.exp (s • A)) s :=
      hasDerivAt_exp_smul_const' A s
    have hrow : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • A) b)
        ((A * NormedSpace.exp (s • A)) b) s :=
      (ContinuousLinearMap.proj (φ := fun _ : V => (V → ℂ)) b).hasFDerivAt.comp_hasDerivAt s hb
    exact (ContinuousLinearMap.proj (φ := fun _ : V => ℂ) a).hasFDerivAt.comp_hasDerivAt s hrow
  have hderiv : ∀ s : ℝ, HasDerivAt
      (fun u : ℝ => ∑ b : V, NormedSpace.exp (u • A) b a) 0 s := by
    intro s
    have hsum : HasDerivAt (fun u : ℝ => ∑ b : V, NormedSpace.exp (u • A) b a)
        (∑ b : V, (A * NormedSpace.exp (s • A)) b a) s :=
      HasDerivAt.fun_sum (u := Finset.univ) fun b _ => hentry b s
    have hzero : (∑ b : V, (A * NormedSpace.exp (s • A)) b a) = 0 := by
      have h1 : ∀ b : V, (A * NormedSpace.exp (s • A)) b a
          = ∑ x : V, A b x * NormedSpace.exp (s • A) x a := fun b => Matrix.mul_apply
      simp only [h1]
      rw [Finset.sum_comm]
      have h2 : ∀ x : V, (∑ b : V, A b x * NormedSpace.exp (s • A) x a)
          = (∑ b : V, A b x) * NormedSpace.exp (s • A) x a :=
        fun x => (Finset.sum_mul (s := Finset.univ) (f := fun b => A b x)
          (a := NormedSpace.exp (s • A) x a)).symm
      simp only [h2, hcol, zero_mul, Finset.sum_const_zero]
    simpa [hzero] using hsum
  have hconst := is_const_of_deriv_eq_zero
    (f := fun u : ℝ => ∑ b : V, NormedSpace.exp (u • A) b a)
    (fun u => (hderiv u).differentiableAt) (fun u => (hderiv u).deriv) t 0
  have hAt : (t : ℝ) • A = (-t : ℝ) • G.lapMatrix ℂ := by
    rw [hA, smul_neg, neg_smul]
  rw [hAt] at hconst
  rw [hconst]
  simp [NormedSpace.exp_zero, Matrix.one_apply]

/-- The real parts of each column of `sourceClassicalKernel` sum to one at every real time. -/
theorem sourceClassicalKernel_mass_one (t : ℝ) (a : V) :
    ∑ b : V, (sourceClassicalKernel G t b a).re = 1 := by
  have h := sourceKernel_column_sum_one G t a
  rw [show (∑ b : V, (sourceClassicalKernel G t b a).re) =
        (∑ b : V, sourceClassicalKernel G t b a).re from
      (Complex.re_sum Finset.univ (fun b => sourceClassicalKernel G t b a)).symm]
  rw [show (∑ b : V, sourceClassicalKernel G t b a) =
        (∑ b : V, NormedSpace.exp ((-t : ℝ) • G.lapMatrix ℂ) b a) from rfl, h]
  simp

end Qatlib.Papers.DecisionTrees97.MainResults
