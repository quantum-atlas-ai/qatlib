/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GenEigenODE20.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# c007 — Corollary 23, Eq. (49)

Shao--Liu, arXiv:2010.15027v2, Corollary 23, p. 18.

For estimating inverse eigenvalues the block-encoding scale is multiplied by
`ρ₀ = max{1, 1/min_{j,λ_j≠0}|λ_j|}`, giving

`Õ(α_A ρ₀ κ_E (T_in + T_A)/ε)`.   (49)

The module proves that (49) is the Corollary 22 complexity with the scale
`α_A` replaced by `α_A ρ₀`, and records nonnegativity.  The relative/additive
alternative in the source's last sentence is an error-accounting choice, not a
different cost; it is recorded in the docstring and is not needed for (49).
-/

set_option autoImplicit false

namespace Qatlib.Papers.GenEigenODE20.MainResults

/-- **Corollary 23 is Corollary 22 with the inverse-eigenvalue scale factor
`ρ₀`.** -/
theorem corollary23_inverse_complexity_eq_standard
    (αA ρ0 κE Tin TA ε : ℝ) :
    inverseEigenComplexity αA ρ0 κE Tin TA ε
      = standardEigenComplexity (αA * ρ0) κE Tin TA ε := by
  unfold inverseEigenComplexity standardEigenComplexity
  ring

/-- The inverse-eigenvalue complexity (49) is nonnegative. -/
theorem corollary23_complexity_nonneg
    (αA ρ0 κE Tin TA ε : ℝ) (hα : 0 ≤ αA) (hρ : 0 ≤ ρ0) (hκ : 0 ≤ κE)
    (hTin : 0 ≤ Tin) (hTA : 0 ≤ TA) (hε : 0 < ε) :
    0 ≤ inverseEigenComplexity αA ρ0 κE Tin TA ε := by
  unfold inverseEigenComplexity
  positivity

end Qatlib.Papers.GenEigenODE20.MainResults
