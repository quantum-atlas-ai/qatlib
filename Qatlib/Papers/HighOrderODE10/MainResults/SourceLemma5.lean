/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HighOrderODE10.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# HighOrderODE10 — Lemma 5: `‖𝓐‖ = O(1)`

Fixed source: Berry, arXiv:1010.2745v2 (28 Jan 2014), Lemma 5 and its proof,
p. 6–7, Eq. (31)–(34).

The paper writes `𝓐 = ∑_{ℓ=0}^{k} 𝓐^{ℓ}` (Eq. (32)) with `𝓐^{ℓ}` block
diagonal (Eq. (31)), uses the triangle inequality (Eq. (33)) and the bound
`‖𝓐^{ℓ}‖ ≤ max_j ‖𝓐^{ℓ}_{j,j}‖` on a block-diagonal matrix, and obtains the
four block bounds of Eq. (34).  Since `h = O(1/‖A‖)` means `h‖A‖ ≤ 1` up to the
absorbed constant, every block bound is `O(1)`, hence `‖𝓐‖ = O(1)`.

Formal content here: `sourceBlockBound m h M ℓ` is exactly the right-hand side
of Eq. (34), `hdecomp` is the triangle-inequality step of Eq. (33), and
`sourceNormCap` is the method-only constant.  The proof is pure real arithmetic.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HighOrderODE10.MainResults

open Finset
open scoped BigOperators

/-- Each block bound of Eq. (34) is bounded by `2 + |α| + |β|` whenever
`0 ≤ h`, `0 ≤ M = ‖A‖` and `hM ≤ 1` (`h = O(1/‖A‖)`). -/
theorem sourceBlockBound_le_cap (m : SourceMultistepMethod) (h M : ℝ)
    (hh : 0 ≤ h) (hM : 0 ≤ M) (hprod : h * M ≤ 1) (ℓ : ℕ) :
    sourceBlockBound m h M ℓ ≤ sourceBlockCap m ℓ := by
  unfold sourceBlockBound sourceBlockCap
  have hbeta : 0 ≤ |betaAt m (sourceCoefIndex m ℓ)| := abs_nonneg _
  have halpha : 0 ≤ |alphaAt m (sourceCoefIndex m ℓ)| := abs_nonneg _
  have hprod' : |betaAt m (sourceCoefIndex m ℓ)| * (h * M) ≤
      |betaAt m (sourceCoefIndex m ℓ)| * 1 :=
    mul_le_mul_of_nonneg_left hprod hbeta
  rw [mul_one] at hprod'
  have hterm : |alphaAt m (sourceCoefIndex m ℓ)| +
      |betaAt m (sourceCoefIndex m ℓ)| * h * M ≤
      |alphaAt m (sourceCoefIndex m ℓ)| + |betaAt m (sourceCoefIndex m ℓ)| := by
    have hrew : |betaAt m (sourceCoefIndex m ℓ)| * h * M =
        |betaAt m (sourceCoefIndex m ℓ)| * (h * M) := by ring
    rw [hrew]
    linarith
  have hhead : (if ℓ = 0 then 1 else if ℓ = 1 then 1 + h * M else 0) ≤ 2 := by
    split_ifs with h0 h1
    · norm_num
    · linarith
    · norm_num
  have hhead' : (if ℓ = 0 then 1 else if ℓ = 1 then 1 + h * M else 0) ≤
      2 + |alphaAt m (sourceCoefIndex m ℓ)| + |betaAt m (sourceCoefIndex m ℓ)| := by
    linarith
  have hterm' : |alphaAt m (sourceCoefIndex m ℓ)| +
      |betaAt m (sourceCoefIndex m ℓ)| * h * M ≤
      2 + |alphaAt m (sourceCoefIndex m ℓ)| + |betaAt m (sourceCoefIndex m ℓ)| := by
    linarith
  exact max_le hhead' hterm'

/-- **Lemma 5** (Berry, arXiv:1010.2745v2, p. 6–7, Eq. (31)–(34)):
if `normScript = ‖𝓐‖` is bounded by the block-diagonal decomposition of
Eq. (33) with the block bounds of Eq. (34), and `h‖A‖ ≤ 1`, then `‖𝓐‖ = O(1)`
with a constant depending only on the multistep method.

In the notation of the paper: `normScript` is `‖𝓐‖`, `M` is `‖A‖`, `hdecomp`
is Eq. (33), `sourceBlockBound m h M ℓ` is Eq. (34), and the witness `C` is
`sourceNormCap m = ∑_{ℓ=0}^{k} (2 + |α_ℓ| + |β_ℓ|)`. -/
theorem lemma5_sourceNorm_isO_one (m : SourceMultistepMethod) (h M normScript : ℝ)
    (hh : 0 ≤ h) (hM : 0 ≤ M) (hprod : h * M ≤ 1)
    (hdecomp : normScript ≤ ∑ ℓ ∈ range (m.k + 1), sourceBlockBound m h M ℓ) :
    ∃ C : ℝ, 0 < C ∧ normScript ≤ C := by
  refine ⟨sourceNormCap m, ?_, ?_⟩
  · unfold sourceNormCap
    refine Finset.sum_pos ?_ ⟨0, by simp⟩
    intro ℓ _
    unfold sourceBlockCap
    positivity
  · calc normScript
        ≤ ∑ ℓ ∈ range (m.k + 1), sourceBlockBound m h M ℓ := hdecomp
      _ ≤ ∑ ℓ ∈ range (m.k + 1), sourceBlockCap m ℓ :=
          Finset.sum_le_sum (fun ℓ _ => sourceBlockBound_le_cap m h M hh hM hprod ℓ)
      _ = sourceNormCap m := rfl

end Qatlib.Papers.HighOrderODE10.MainResults
