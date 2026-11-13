/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonSparseHam09.MainResults.Defs
import Qatlib.Papers.NonSparseHam09.MainResults.NormChain

/-!
# Arboricity norm-bound proposition

Defines `prop2Statement`, the three norm bounds associated with a supplied arboricity bound for
a Hermitian matrix's graph. The proved auxiliary results establish the spectral-norm triangle
inequality, nonnegative homogeneity, and entrywise nonnegativity of `absMatrix`. See
[ChildsKothari2010] for the surrounding analysis.

## Main statements

* `prop2Statement`: The proposition asserting that the complex entrywise absolute-value matrix
  has spectral norm at most `2 * k * mcnNorm H` and `2 * k * specNorm H`, and that `specNorm H ≤
  2 * k * mcnNorm H`.
* `specNorm_add_le`: The spectral norm of a sum of two matrices is at most the sum of their
  spectral norms.
* `specNorm_smul_nonneg`: Multiplication by a nonnegative real scalar multiplies the spectral
  norm by that scalar.

## References

* [Childs and Kothari, 2010][ChildsKothari2010]
-/

set_option autoImplicit false
noncomputable section

open Matrix Finset
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.NonSparseHam09.MainResults

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The proposition asserting that the complex entrywise absolute-value matrix has spectral norm
at most `2 * k * mcnNorm H` and `2 * k * specNorm H`, and that `specNorm H ≤ 2 * k * mcnNorm
H`. -/
def prop2Statement (H : Matrix ι ι ℂ) (_hH : H.IsHermitian) {k : ℕ}
    (_hk : GraphArboricityLE (matrixGraph H) k) : Prop :=
  specNorm ((absMatrix H).map Complex.ofReal) ≤ 2 * (k : ℝ) * mcnNorm H ∧
  specNorm ((absMatrix H).map Complex.ofReal) ≤ 2 * (k : ℝ) * specNorm H ∧
  specNorm H ≤ 2 * (k : ℝ) * mcnNorm H

/-- The spectral norm of a sum of two matrices is at most the sum of their spectral norms
[ChildsKothari2010]. -/
theorem specNorm_add_le (A B : Matrix ι ι ℂ) :
    specNorm (A + B) ≤ specNorm A + specNorm B := by
  rw [specNorm_eq_l2, specNorm_eq_l2, specNorm_eq_l2]
  exact norm_add_le A B

/-- Multiplication by a nonnegative real scalar multiplies the spectral norm by that scalar
[ChildsKothari2010]. -/
lemma specNorm_smul_nonneg {c : ℝ} (hc : 0 ≤ c) (A : Matrix ι ι ℂ) :
    specNorm (c • A) = c * specNorm A := by
  rw [specNorm_eq_l2, specNorm_eq_l2, norm_smul, Real.norm_of_nonneg hc]

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in

/-- Every entry of `absMatrix H` is nonnegative [ChildsKothari2010]. -/
lemma absMatrix_nonneg (H : Matrix ι ι ℂ) (i j : ι) : 0 ≤ absMatrix H i j :=
  norm_nonneg _

end Qatlib.Papers.NonSparseHam09.MainResults
