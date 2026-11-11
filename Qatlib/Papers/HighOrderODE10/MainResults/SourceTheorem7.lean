/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HighOrderODE10.MainResults.SourceLemma5
import Qatlib.Papers.HighOrderODE10.MainResults.SourceLemma6

set_option backward.isDefEq.respectTransparency false

/-!
# HighOrderODE10 — Theorem 7: `κ(𝓐) = O(N_t κ_V)`

Fixed source: Berry, arXiv:1010.2745v2 (28 Jan 2014), Theorem 7 and its proof,
p. 9, Eq. (53).

The proof is one line in the paper: the condition number is
`κ = ‖𝓐‖·‖𝓐⁻¹‖` (Eq. (53)), and the hypotheses of Theorem 7 are exactly the
hypotheses of Lemmas 5 and 6, so the two bounds multiply to `O(N_t κ_V)`.

Here the two lemma conclusions are passed as explicit bounds (`h5`, `h6`) and
the multiplication is carried out concretely: the witness is `C5 * C6`.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HighOrderODE10.MainResults

/-- **Theorem 7** (Berry, arXiv:1010.2745v2, p. 9, Eq. (53)).
Suppose the multistep method is `A(α)`-stable, `A = V D V⁻¹`, the eigenvalues
satisfy `|arg(-λ_i)| ≤ α`, and `h = O(1/‖A‖)`.  Lemma 5 then gives
`‖𝓐‖ = O(1)` and Lemma 6 gives `‖𝓐⁻¹‖ = O(N_t κ_V)`.  Since the condition
number is `κ = ‖𝓐‖‖𝓐⁻¹‖`, we obtain `κ = O(N_t κ_V)`.

`normScript` is `‖𝓐‖`, `normInvScript` is `‖𝓐⁻¹‖`, `kappaV` is `κ_V`,
`Nt` is the number of time steps, and `kappa` is the condition number `κ`.
-/
theorem theorem7_conditionNumber_isO
    (Nt kappaV normScript normInvScript kappa : ℝ)
    (hNt : 0 ≤ Nt) (hkappaV : 0 ≤ kappaV)
    (hInvNonneg : 0 ≤ normInvScript)
    (hcond : kappa = normScript * normInvScript)
    (h5 : ∃ C : ℝ, 0 < C ∧ normScript ≤ C)
    (h6 : ∃ C : ℝ, 0 < C ∧ normInvScript ≤ C * Nt * kappaV) :
    ∃ C : ℝ, 0 < C ∧ kappa ≤ C * Nt * kappaV := by
  obtain ⟨C5, hC5, hA⟩ := h5
  obtain ⟨C6, hC6, hI⟩ := h6
  refine ⟨C5 * C6, mul_pos hC5 hC6, ?_⟩
  rw [hcond]
  have hC5nonneg : 0 ≤ C5 := le_of_lt hC5
  calc normScript * normInvScript
      ≤ C5 * (C6 * Nt * kappaV) :=
        mul_le_mul hA hI hInvNonneg hC5nonneg
    _ = (C5 * C6) * Nt * kappaV := by ring

end Qatlib.Papers.HighOrderODE10.MainResults
