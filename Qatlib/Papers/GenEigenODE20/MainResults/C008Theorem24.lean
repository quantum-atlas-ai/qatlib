/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GenEigenODE20.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# c008 — Theorem 24, Eq. (50)

Shao--Liu, arXiv:2010.15027v2, Theorem 24, p. 19.

For Hermitian `A` and positive-definite `B`, with block-encoding scales
`α_A, α_B` and synthesis times `T_A, T_B`, the algorithm estimates the
generalized eigenvalues in time

`Õ( κ_B^{0.5} T_in + (α_A κ_B^{1.5}/(‖B‖ ε)) (T_A + α_B κ_B T_B/‖B‖) )`.  (50)

The fractional power is written `κ_B^{1.5} = κ_B √κ_B`.  This module proves the
factored form used by the paper's derivation: the second term is the product of
the Hermitian block-encoding prefactor `α_A κ_B^{1.5}/(‖B‖ ε)` with the
per-run synthesis budget `T_A + α_B κ_B T_B/‖B‖`, and records nonnegativity.
-/

set_option autoImplicit false

namespace Qatlib.Papers.GenEigenODE20.MainResults

/-- **The factored form of Eq. (50).**  The displayed Hermitian-GEP complexity
is the input cost plus the block-encoding prefactor times the synthesis
budget. -/
theorem theorem24_hermitian_decomposition
    (κB αA αB Tin TA TB Bnorm ε : ℝ) :
    hermitianComplexity κB αA αB Tin TA TB Bnorm ε
      = Real.sqrt κB * Tin +
        (αA * (κB * Real.sqrt κB) / (Bnorm * ε)) *
          (TA + αB * κB * TB / Bnorm) := by
  unfold hermitianComplexity
  ring

/-- The Hermitian-GEP complexity (50) is nonnegative under the paper's sign
conditions. -/
theorem theorem24_complexity_nonneg
    (κB αA αB Tin TA TB Bnorm ε : ℝ)
    (hκ : 0 ≤ κB) (hαA : 0 ≤ αA) (hαB : 0 ≤ αB) (hTin : 0 ≤ Tin)
    (hTA : 0 ≤ TA) (hTB : 0 ≤ TB) (hB : 0 < Bnorm) (hε : 0 < ε) :
    0 ≤ hermitianComplexity κB αA αB Tin TA TB Bnorm ε := by
  unfold hermitianComplexity
  positivity

end Qatlib.Papers.GenEigenODE20.MainResults
