/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.TaylorAnalysis.Theorem5Aux4
import Qatlib.Papers.QLinearODE17.TaylorAnalysis.Theorem5Norm

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 3 of `QLinearODE17`: the inverse norm of the Taylor system

Source: arXiv:1701.03684v2, Section 2 (printed Lemma 3, `lem:nminv`).
For a diagonalizable `A = V D V⁻¹` with `|λ_i| ≤ 1`, `Re λ_i ≤ 0` on the
diagonal of `D`, `m, k, p ≥ 1`, `k ≥ 5` and `(k+1)! ≥ 2m`,
`‖C_{m,k,p}(A)⁻¹‖ ≤ 3 κ_V √k (m+p)` with `κ_V = ‖V‖ ‖V⁻¹‖`.

The printed proof diagonalizes `C(A) = Ṽ C(D) Ṽ⁻¹` with `κ_Ṽ = κ_V`, bounds the
diagonal inverse column-by-column (Lemma 2), and combines the two factors. The
Frozen development already carries both halves as separate declarations:
`taylorV2_inverse_norm_transport` (the dimension-free similarity transport) and
`taylorV2_diagonal_inverse_norm_le` (the diagonal case through the real scalar
inverse columns). This module is the paper-level bridge that composes them into
the printed single statement; no new mathematical content is introduced.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QLinearODE17.TaylorAnalysis

open Qatlib.Papers.QLinearODE17.TaylorAnalysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {N : Type} [Fintype N] [DecidableEq N]

/-- Printed Lemma 3: the inverse of the order-`(m,k,p)` Taylor system in the
actual diagonalizable matrix `A` is bounded by
`3 ‖V‖ ‖V⁻¹‖ √k (m+p)`. -/
theorem lemma3_inverse_norm_le (m k p : ℕ) (A V D : Matrix N N ℂ)
    (hm : 0 < m) (hk : 5 ≤ k) (hp : 0 < p) (hfac : 2 * m ≤ Nat.factorial (k + 1))
    (hAV : A * V = V * D) (hV1 : V * V⁻¹ = 1) (hV2 : V⁻¹ * V = 1)
    (hd : ∀ i j : N, i ≠ j → D i j = 0) (hz : ∀ n, ‖D n n‖ ≤ 1)
    (hre : ∀ n, (D n n).re ≤ 0) :
    ‖(taylorStepMatrixV2 m k p A)⁻¹‖ ≤
      3 * (‖V‖ * ‖V⁻¹‖) * Real.sqrt (k : ℝ) * ((m + p : ℕ) : ℝ) := by
  have htrans := taylorV2_inverse_norm_transport m k p A V D hAV hV1 hV2
  have hdiag := taylorV2_diagonal_inverse_norm_le m k p D hm hk hp hfac hd hz hre
  calc ‖(taylorStepMatrixV2 m k p A)⁻¹‖
      ≤ (‖V‖ * ‖V⁻¹‖) * ‖(taylorStepMatrixV2 m k p D)⁻¹‖ := htrans
    _ ≤ (‖V‖ * ‖V⁻¹‖) * (3 * Real.sqrt (k : ℝ) * ((m + p : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hdiag (by positivity)
    _ = 3 * (‖V‖ * ‖V⁻¹‖) * Real.sqrt (k : ℝ) * ((m + p : ℕ) : ℝ) := by ring

end Qatlib.Papers.QLinearODE17.TaylorAnalysis
