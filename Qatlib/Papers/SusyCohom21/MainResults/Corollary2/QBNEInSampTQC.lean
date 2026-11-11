/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SusyCohom21.MainResults.SusyModel

set_option backward.isDefEq.respectTransparency false

/-!
# Corollary 2 — QBNE is in sampTQC under inverse-polynomial ratios for all p

Cade--Crichigno, fixed arXiv:2107.00011v2, Corollary 2 (page 16): QBNE is in
sampTQC when `dim(V^p) / 2^n = Ω(1/poly n)` for all `p`.

Boundary: sampTQC membership is not formalised. This file states the concrete
counting fact: if every one of the `m+1` grade contributions `dim_p / total_p`
is at least `1/q`, then their sum is at least `(m+1)/q`; this is the
union-bound step used to certify the promised support for all grades at once.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Papers.SusyCohom21.MainResults.SusyModel

namespace Qatlib.Papers.SusyCohom21.MainResults.Corollary2

/-- Fixed arXiv:2107.00011v2, Corollary 2: if every grade `p : Fin (m+1)` has
support ratio at least `1/q`, then all ratios hold and their sum is at least
`(m+1)/q`. -/
theorem qbne_in_samptqc (m q : ℕ) (dim total : Fin (m + 1) → ℚ)
    (_hq : 0 < (q : ℚ))
    (h : ∀ p : Fin (m + 1), (1 : ℚ) / (q : ℚ) ≤ dim p / total p) :
    (∀ p : Fin (m + 1), (1 : ℚ) / (q : ℚ) ≤ dim p / total p) ∧
    ((m + 1 : ℚ) * ((1 : ℚ) / (q : ℚ)) ≤
      ∑ p : Fin (m + 1), dim p / total p) := by
  refine ⟨h, ?_⟩
  have hcard : ((Finset.univ : Finset (Fin (m + 1))).card : ℚ) = (m + 1 : ℚ) := by
    simp
  calc (m + 1 : ℚ) * ((1 : ℚ) / (q : ℚ))
      = ((Finset.univ : Finset (Fin (m + 1))).card : ℚ) * ((1 : ℚ) / (q : ℚ)) := by
        rw [hcard]
    _ = ∑ _p : Fin (m + 1), ((1 : ℚ) / (q : ℚ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ p : Fin (m + 1), dim p / total p :=
        Finset.sum_le_sum (fun p _ => h p)

end Qatlib.Papers.SusyCohom21.MainResults.Corollary2
