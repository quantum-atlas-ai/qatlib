/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Square-root frames for stochastic rows

Defines `rowFrame P`, whose column at `x` is supported on pairs with first coordinate `x` and
has entries `√(P x y)`. The theorem `rowFrame_gram` shows that a row-stochastic matrix produces
an isometric frame. See [ClaudonPiquemalMonmarche2025] for related background.

## Main statements

* `rowFrame_gram`: For row-stochastic `P`, the square-root row frame satisfies `(rowFrame P)ᴴ *
  rowFrame P = 1`.

## References

* [Claudon et al., 2025][ClaudonPiquemalMonmarche2025]
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Foundations.MatrixGeometry.StochasticFrame
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The complex matrix with entry `√(P x y)` at row `(x, y)` in column `x`, and zero whenever
the row's first coordinate differs from the column index. -/
noncomputable def rowFrame (P : I → I → ℝ) : Matrix (I × I) I ℂ :=
  Matrix.of fun p x => if p.1 = x then ((Real.sqrt (P x p.2) : ℂ)) else 0

/-- For row-stochastic `P`, the square-root row frame satisfies `(rowFrame P)ᴴ * rowFrame P =
1`. -/
theorem rowFrame_gram (P : I → I → ℝ) (hP : P ∈ Matrix.rowStochastic ℝ I) :
    (rowFrame P)ᴴ * rowFrame P = 1 := by
  ext x x'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def,
    rowFrame, Matrix.of_apply, Matrix.one_apply]
  by_cases hxx' : x = x'
  · subst hxx'
    have hkey : ∀ p : I × I,
        (starRingEnd ℂ) (if p.1 = x then ((Real.sqrt (P x p.2) : ℂ)) else 0)
            * (if p.1 = x then ((Real.sqrt (P x p.2) : ℂ)) else 0)
          = if p.1 = x then ((P x p.2 : ℂ)) else 0 := by
      intro p
      by_cases hp : p.1 = x
      · rw [if_pos hp, if_pos hp, Complex.conj_ofReal, ← Complex.ofReal_mul, ← sq,
          Real.sq_sqrt (hP.1 x p.2)]
      · rw [if_neg hp, if_neg hp, map_zero, zero_mul]
    rw [Finset.sum_congr rfl (fun p _ => hkey p), Fintype.sum_prod_type,
      Finset.sum_eq_single x]
    · simp only [if_true]
      exact_mod_cast Matrix.sum_row_of_mem_rowStochastic hP x
    · intro a _ ha
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [if_neg (fun e : (a, y).1 = x => ha e)]
    · intro hcon
      exact absurd (Finset.mem_univ x) hcon
  · have hzero : ∀ p : I × I,
        (starRingEnd ℂ) (if p.1 = x then ((Real.sqrt (P x p.2) : ℂ)) else 0)
            * (if p.1 = x' then ((Real.sqrt (P x' p.2) : ℂ)) else 0) = 0 := by
      intro p
      by_cases hp : p.1 = x
      · simp only [if_pos hp,
          if_neg (show ¬(p.1 = x') from fun e => hxx' (hp.symm.trans e)), mul_zero]
      · simp only [if_neg hp, map_zero, zero_mul]
    rw [Finset.sum_eq_zero (fun p _ => hzero p), if_neg hxx']

end Qatlib.Foundations.MatrixGeometry.StochasticFrame
