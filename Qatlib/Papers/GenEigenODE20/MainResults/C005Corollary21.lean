/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GenEigenODE20.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# c005 — Corollary 21, Eq. (47)

Shao--Liu, arXiv:2010.15027v2, Corollary 21, p. 18.

For `s_A`- and `s_B`-sparse `A` and `B`, the sparse-access block encodings have
scales `s_A ‖A‖_max` and `s_B ‖B‖_max` and unit synthesis time, so the general
Theorem 20 run time (43) specialises to

`Õ( (κ_E/ε) ((s_A‖A‖_max + ρ s_B‖B‖_max) T_in) ‖B⁻¹‖ )`.   (47)

The module proves that the displayed sparse complexity (47) is *exactly* the
general complexity of Theorem 20 under the substitution
`α_A = s_A ‖A‖_max`, `α_B = s_B ‖B‖_max`, `T_A = T_B = 0`, and records its
nonnegativity.
-/

set_option autoImplicit false

namespace Qatlib.Papers.GenEigenODE20.MainResults

/-- **Corollary 21 is Theorem 20 with sparse-access scales and zero synthesis
times.** -/
theorem corollary21_sparse_complexity_eq_theorem20
    (κE ε sA sB Amax Bmax ρ Tin BinvNorm : ℝ) :
    sparseGEPComplexity κE ε sA sB Amax Bmax ρ Tin BinvNorm
      = thm20Complexity κE ε (sA * Amax) (sB * Bmax) ρ Tin 0 0 BinvNorm := by
  unfold sparseGEPComplexity thm20Complexity
  ring

/-- The sparse GEP complexity (47) is nonnegative under the paper's sign
conditions. -/
theorem corollary21_complexity_nonneg
    (κE ε sA sB Amax Bmax ρ Tin BinvNorm : ℝ)
    (hκ : 0 ≤ κE) (hε : 0 < ε) (hsA : 0 ≤ sA) (hsB : 0 ≤ sB)
    (hAmax : 0 ≤ Amax) (hBmax : 0 ≤ Bmax) (hρ : 0 ≤ ρ)
    (hTin : 0 ≤ Tin) (hB : 0 ≤ BinvNorm) :
    0 ≤ sparseGEPComplexity κE ε sA sB Amax Bmax ρ Tin BinvNorm := by
  unfold sparseGEPComplexity
  positivity

end Qatlib.Papers.GenEigenODE20.MainResults
