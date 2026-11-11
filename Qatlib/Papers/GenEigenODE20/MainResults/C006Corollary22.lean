/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GenEigenODE20.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# c006 — Corollary 22, Eq. (48)

Shao--Liu, arXiv:2010.15027v2, Corollary 22, p. 18.

For the standard eigenproblem `A x = λ x` (`B = I`), Theorem 20 specialises to

`Õ(α_A κ_E (T_in + T_A)/ε)`.   (48)

The module proves that (48) is exactly the Theorem 20 complexity with
`α_B = 0`, `T_B = 0`, `ρ = 1` and `‖B⁻¹‖ = 1`, and records nonnegativity.
-/

set_option autoImplicit false

namespace Qatlib.Papers.GenEigenODE20.MainResults

/-- **Corollary 22 is Theorem 20 at `B = I`.** -/
theorem corollary22_standard_complexity_eq_theorem20
    (αA κE Tin TA ε : ℝ) :
    standardEigenComplexity αA κE Tin TA ε
      = thm20Complexity κE ε αA 0 1 Tin TA 0 1 := by
  unfold standardEigenComplexity thm20Complexity
  ring

/-- The standard eigenvalue-estimation complexity (48) is nonnegative. -/
theorem corollary22_complexity_nonneg
    (αA κE Tin TA ε : ℝ) (hα : 0 ≤ αA) (hκ : 0 ≤ κE)
    (hTin : 0 ≤ Tin) (hTA : 0 ≤ TA) (hε : 0 < ε) :
    0 ≤ standardEigenComplexity αA κE Tin TA ε := by
  unfold standardEigenComplexity
  positivity

end Qatlib.Papers.GenEigenODE20.MainResults
