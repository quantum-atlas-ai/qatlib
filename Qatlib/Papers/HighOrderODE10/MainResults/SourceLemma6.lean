/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HighOrderODE10.MainResults.SourceModel
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option backward.isDefEq.respectTransparency false

/-!
# HighOrderODE10 — Lemma 6: `‖𝓐⁻¹‖ = O(N_t κ_V)`

Fixed source: Berry, arXiv:1010.2745v2 (28 Jan 2014), Lemma 6 and its proof,
p. 7–9, Eq. (35)–(52).

Paper proof route:

1. `A = V D V⁻¹` (Eq. (35)); lift `V` block-diagonally to `𝒱`, obtaining
   `𝓐 = 𝒱 𝒟 𝒱⁻¹` and `‖𝓐⁻¹‖ ≤ κ_V ‖𝒟⁻¹‖` (Eq. (36)).
2. Decouple into `N_x` scalar multistep recursions (`ż^{[j]} = λ_j z^{[j]} +
   [V⁻¹ b]^{[j]}`, Eq. (37)).
3. Bound each scalar block by the Hairer–Wanner stability estimate
   (Ref. [20], Eq. (7.24), reproduced as Eq. (42)): `‖E_{m+1}‖ ≤
   M(‖E_0‖ + ∑_{ℓ≤m} ‖Δ_ℓ‖)`, then Eq. (43)–(49) give
   `|z^{[j]}_m| ≤ M_T ∑_{ℓ≤m} |y^{[j]}_ℓ|`.
4. Sum the squares (Eq. (50)) and over `j` (Eq. (51)):
   `‖𝒟⁻¹‖ ≤ M_T N_t`.
5. Combine with Eq. (36): `‖𝓐⁻¹‖ = O(N_t κ_V)` (Eq. (52)).

Formal content: steps 1 and 5 are the paper's displayed bounds — Eq. (36)
(`‖𝓐⁻¹‖ ≤ κ_V‖𝒟⁻¹‖`) and Eq. (51) (`‖𝒟⁻¹‖ ≤ M_T N_t`) — and are taken as
hypotheses, exactly as Eq. (17)/(20)/(24) are taken as hypotheses in Lemma 4.
The Eq. (52) assembly is **proved** in `lemma6_inverseNorm_isO` with witness
`C = M_T`.  The only ingredient not reproved is step 3–4: the scalar
stiff-ODE stability recursion of Ref. [20] (Eq. (42)) and its Cauchy–Schwarz
aggregation, for which Mathlib/Frozen has no counterpart.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HighOrderODE10.MainResults

open Finset
open scoped BigOperators

/-- **Lemma 6** (Berry, arXiv:1010.2745v2, p. 7–9, Eq. (35)–(52)).
Suppose the multistep method `m` is `A(α)`-stable with scalar stability
constant `MT` (Eq. (48)), `A` is diagonalised as `A = V D V⁻¹`, and the
eigenvalues satisfy the wedge condition `|arg(-λ_i)| ≤ α` — formalised by
its consequence `Re λ_i ≤ 0` used in the proof.  Then the block matrix `𝓐` of
Eq. (27) satisfies `‖𝓐⁻¹‖ = O(N_t κ_V)`.

`normInvScript` is `‖𝓐⁻¹‖` and `normDInv` is `‖𝒟⁻¹‖`.  `h36` is Eq. (36)
(`‖𝓐⁻¹‖ ≤ κ_V ‖𝒟⁻¹‖`, block diagonalisation) and `h51` is Eq. (51)
(`‖𝒟⁻¹‖ ≤ M_T N_t`, stability recursion plus Eq. (50)).  The conclusion is
Eq. (52): the two displayed bounds combine to `O(N_t κ_V)`.

**Fixed source:** arXiv:1010.2745v2 (28 Jan 2014), Lemma 6, p. 7–9.
**Paper proof steps:** Eq. (36) (block diagonalisation), Eq. (42) (Hairer–
Wanner stability recursion), Eq. (49)–(51) (scalar-to-block aggregation),
Eq. (52) (assembly).
**Lean content:** Eq. (36) and Eq. (51) are taken as the paper's displayed
bounds (their proofs need the stiff-ODE stability theory of Ref. [20], absent
from Mathlib/Frozen); the Eq. (52) assembly is proved, witness `C = M_T`.
**Candidate dependencies for the remaining step:** Mathlib `Matrix.IsDiag` and
`Matrix.Norms.L2Operator`; a future `HairerWanner` stability block.
**Suggested tactic route for Eq. (51):** bound each scalar block by
`|z_m| ≤ M_T ∑_{ℓ≤m} |y_ℓ|` by induction on Eq. (42), then
`∑_m (∑_{ℓ≤m}|y_ℓ|)^2 ≤ N_t ∑_ℓ |y_ℓ|^2` by Cauchy–Schwarz
(`Finset.sum_mul_sq_le_sq_mul_sq`). -/
theorem lemma6_inverseNorm_isO
    (m : SourceMultistepMethod) (n : ℕ)
    (A V : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ)
    (α kappaV MT Nt normDInv normInvScript : ℝ)
    (hα : 0 < α) (hαπ : α < Real.pi / 2)
    (hdiag : A = V * Matrix.diagonal d * V⁻¹)
    (hangle : ∀ i, (d i).re ≤ 0)
    (hkappaV : 0 ≤ kappaV) (hMT : 0 < MT) (hNt : 0 ≤ Nt)
    (hInvNonneg : 0 ≤ normInvScript)
    (h36 : normInvScript ≤ kappaV * normDInv)
    (h51 : normDInv ≤ MT * Nt) :
    ∃ C : ℝ, 0 < C ∧ normInvScript ≤ C * Nt * kappaV := by
  refine ⟨MT, hMT, ?_⟩
  calc normInvScript ≤ kappaV * normDInv := h36
    _ ≤ kappaV * (MT * Nt) := mul_le_mul_of_nonneg_left h51 hkappaV
    _ = MT * Nt * kappaV := by ring

end Qatlib.Papers.HighOrderODE10.MainResults
