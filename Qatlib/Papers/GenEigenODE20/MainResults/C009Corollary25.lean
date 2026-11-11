/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GenEigenODE20.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# c009 — Corollary 25, Eq. (54)

Shao--Liu, arXiv:2010.15027v2, Corollary 25, p. 21.

For sparse Hermitian `A, B` with `B` positive definite, Theorem 24 specialises
to

`Õ( κ_B^{0.5} T_in + κ_B^{2.5} s_A s_B ‖A‖_max ‖B‖_max/(ε ‖B‖²) )`.  (54)

The paper obtains (54) from the Hermitian bound (50) by inserting the
sparse-access scales `α_A = s_A‖A‖_max`, `α_B = s_B‖B‖_max` and unit synthesis
times, and then dropping the (nonnegative) lower-order synthesis term.  This
module proves the resulting inequality between the two displayed expressions:
the sparse bound is at most the corresponding Hermitian bound with those
substitutions.
-/

set_option autoImplicit false

namespace Qatlib.Papers.GenEigenODE20.MainResults

/-- **Corollary 25 is dominated by the substituted Theorem 24 bound.**  Setting
`α_A = s_A‖A‖_max`, `α_B = s_B‖B‖_max`, `T_A = T_B = 1` in (50) leaves the
sparse complexity (54) plus the nonnegative term
`s_A‖A‖_max κ_B^{1.5}/(‖B‖ε)`. -/
theorem corollary25_sparse_le_hermitian
    (κB sA sB Amax Bmax Tin Bnorm ε : ℝ)
    (hκ : 0 ≤ κB) (hsA : 0 ≤ sA) (hsB : 0 ≤ sB)
    (hAmax : 0 ≤ Amax) (hBmax : 0 ≤ Bmax) (hTin : 0 ≤ Tin)
    (hB : 0 < Bnorm) (hε : 0 < ε) :
    sparseHermitianComplexity κB sA sB Amax Bmax Tin Bnorm ε
      ≤ hermitianComplexity κB (sA * Amax) (sB * Bmax) Tin 1 1 Bnorm ε := by
  have hdiff : hermitianComplexity κB (sA * Amax) (sB * Bmax) Tin 1 1 Bnorm ε
      - sparseHermitianComplexity κB sA sB Amax Bmax Tin Bnorm ε
      = (sA * Amax) * (κB * Real.sqrt κB) / (Bnorm * ε) := by
    unfold hermitianComplexity sparseHermitianComplexity
    field_simp
    ring
  have hterm : 0 ≤ (sA * Amax) * (κB * Real.sqrt κB) / (Bnorm * ε) := by
    positivity
  linarith

/-- The sparse Hermitian complexity (54) is nonnegative under the paper's sign
conditions. -/
theorem corollary25_complexity_nonneg
    (κB sA sB Amax Bmax Tin Bnorm ε : ℝ)
    (hκ : 0 ≤ κB) (hsA : 0 ≤ sA) (hsB : 0 ≤ sB)
    (hAmax : 0 ≤ Amax) (hBmax : 0 ≤ Bmax) (hTin : 0 ≤ Tin)
    (hB : 0 < Bnorm) (hε : 0 < ε) :
    0 ≤ sparseHermitianComplexity κB sA sB Amax Bmax Tin Bnorm ε := by
  unfold sparseHermitianComplexity
  positivity

end Qatlib.Papers.GenEigenODE20.MainResults
