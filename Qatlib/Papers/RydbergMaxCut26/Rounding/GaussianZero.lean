/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianEndpoints
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric

/-!
# The rank-three BOV kernel at zero correlation

The function `bovThreeKernel` is the hypergeometric expression for rank-three normalized
Gaussian projection correlations. This module verifies its value at zero and matches it with
`rawExpectation` for orthogonal inputs. See [CrostaSaubanereHuber2026].

## Main statements

* `bovThreeKernel`: defines the rank-three hypergeometric kernel.
* `bov_three_orthogonal`: proves the kernel identity for orthogonal input vectors.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianMatrix

/-- The rank-three BOV kernel `(8 / (3 * π)) * t * ₂F₁(1/2, 1/2; 5/2; t²)` from the normalized
Gaussian projection formula in [Crosta et al., Lemma 5][CrostaSaubanereHuber2026]. -/
def bovThreeKernel (t : ℝ) : ℝ := (8/(3*Real.pi))*t*₂F₁ (1/2:ℝ) (1/2) (5/2) (t^2)

/-- The rank-three BOV kernel vanishes at zero. -/
theorem bovThreeKernel_zero : bovThreeKernel 0=0 := by simp [bovThreeKernel]

/-- For orthogonal input vectors, the raw Gaussian rounding expectation equals the rank-three
BOV kernel evaluated at their inner product. -/
theorem bov_three_orthogonal {I : Type} [Fintype I] (u v : Row I) (h : inner ℝ u v=0) :
    rawExpectation u v=bovThreeKernel (inner ℝ u v) := by
  rw [rawExpectation_eq,matrixExpectation_orthogonal u v h,h,bovThreeKernel_zero]

end Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianMatrix
