/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TrotterSuzuki15.MainResults.SourceTermCount.SourceTermCountModel

set_option backward.isDefEq.respectTransparency false

/-!
# TermCountBound — Eq. (5) of arXiv:1512.03416v1

Fixed paper version: arXiv:1512.03416v1 (R. D. Somma, 10 December 2015).
Source: p. 2, Eq. (5)–(6), and the derivation on p. 3, Eqs. (12)–(14).

The paper: for finite-dimensional `g` and `y t ≥ ε`,
`N = O(5^{2p} L^{2+1/p} β y^{1/(2p)} t^{1+1/(2p)} / ε^{1/(2p)})` (Eq. (5)),
with `β := maxΣ|γ|` from Eq. (6) and `y := max‖ĥ_k U(λ)|ψ⟩‖`.  The proof
(Eq. (13)–(14)) uses `β_{j+1} ≤ β^j y`, `f_j ≤ 6`, and chooses
`r = ⌈5^{p+2} L^{1+1/p} β y^{1/(2p)} t^{1+1/(2p)}/ε^{1/(2p)}⌉` (Eq. (14)),
then multiplies by `N_p` to reach Eq. (5).

What is formalised here is exactly that last multiplication with an explicit
constant: `N = r N_p` as defined in `SourceTermCountModel` (the segment count is
Eq. (14)), and `N ≤ 20 · (Eq. (5) shape) + N_p`, the additive `N_p` being the
rounding of `⌈·⌉`.  In the regime where Eq. (14) gives at least one segment
(`1 ≤ sourceSegmentReal`, the paper's "suffices to choose r" reading of
`y t ≥ ε`), the additive term is absorbed and the clean bound
`N ≤ 20 · (Eq. (5) shape)` holds.

The abstract Lie-algebra constants `β`, `y` are kept as the paper's real
parameters; the concrete matrix-side certificate `pfCommAlphaSelf` enters through
the frozen `g17` bridge in `SourceMainTheorem`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TrotterSuzuki15.MainResults.SourceTermCount

/-- Eq. (14) × `N_p` (arXiv:1512.03416v1, p. 3): the real segment count times
`N_p = 2L5^{p-1}` equals `10` times the Eq. (5) shape, since
`5^{p+2}·5^{p-1} = 5·5^{2p}` and `L^{1+1/p}·L = L^{2+1/p}`. -/
theorem sourceSegmentReal_mul_macro {p : ℕ} (hp : 1 ≤ p) {L β y t ε : ℝ}
    (hL : 0 < L) (hβ : 0 ≤ β) :
    sourceSegmentReal p L β y t ε * sourceMacroCount L p =
      10 * eq5Bound p L β y t ε := by
  have h5 : (5 : ℝ) ^ (p + 2) * (5 : ℝ) ^ (p - 1) = (5 : ℝ) * (5 : ℝ) ^ (2 * p) := by
    rw [← pow_add]
    have he : p + 2 + (p - 1) = 2 * p + 1 := by omega
    rw [he, pow_succ']
  have hLp : L ^ (1 + 1 / (p : ℝ)) * L = L ^ (2 + 1 / (p : ℝ)) := by
    have h : L ^ (2 + 1 / (p : ℝ)) = L ^ (1 + 1 / (p : ℝ)) * L ^ (1 : ℝ) := by
      rw [← Real.rpow_add hL]
      congr 1
      ring
    rw [h, Real.rpow_one]
  unfold sourceSegmentReal sourceMacroCount eq5Bound
  rw [show (5 : ℝ) ^ (p + 2) * L ^ (1 + 1 / (p : ℝ)) * β *
        y ^ (1 / (2 * (p : ℝ))) * t ^ (1 + 1 / (2 * (p : ℝ))) /
        ε ^ (1 / (2 * (p : ℝ))) * (2 * L * 5 ^ (p - 1)) =
      ((5 : ℝ) ^ (p + 2) * (5 : ℝ) ^ (p - 1)) *
        (L ^ (1 + 1 / (p : ℝ)) * L) * (2 * β) *
        y ^ (1 / (2 * (p : ℝ))) * t ^ (1 + 1 / (2 * (p : ℝ))) /
        ε ^ (1 / (2 * (p : ℝ))) by ring]
  rw [h5, hLp]
  ring

/-- **Eq. (5), derived form (arXiv:1512.03416v1, p. 2–3)**: for `p ≥ 1`, `L ≥ 1`,
`β ≥ 1`, the total number of exponentials `N = r N_p` with the Eq. (14) segment
count satisfies `N ≤ 20 · 5^{2p} L^{2+1/p} β y^{1/(2p)} t^{1+1/(2p)}/ε^{1/(2p)}
+ N_p`. -/
theorem sourceNumTerms_le_eq5 {p : ℕ} (hp : 1 ≤ p) {L β y t ε : ℝ}
    (hL : 1 ≤ L) (hβ : 1 ≤ β) (hy : 0 ≤ y) (ht : 0 ≤ t) (hε : 0 < ε) :
    sourceNumTerms p L β y t ε ≤ 20 * eq5Bound p L β y t ε + sourceMacroCount L p := by
  have hLpos : (0 : ℝ) < L := by linarith
  have hβ0 : (0 : ℝ) ≤ β := by linarith
  have hx0 : 0 ≤ sourceSegmentReal p L β y t ε := by
    unfold sourceSegmentReal
    have h1 : (0 : ℝ) ≤ (5 : ℝ) ^ (p + 2) := by positivity
    have h2 : (0 : ℝ) ≤ L ^ (1 + 1 / (p : ℝ)) := Real.rpow_nonneg hLpos.le _
    have h3 : (0 : ℝ) ≤ y ^ (1 / (2 * (p : ℝ))) := Real.rpow_nonneg hy _
    have h4 : (0 : ℝ) ≤ t ^ (1 + 1 / (2 * (p : ℝ))) := Real.rpow_nonneg ht _
    have h5 : (0 : ℝ) ≤ ε ^ (1 / (2 * (p : ℝ))) := (Real.rpow_pos_of_pos hε _).le
    exact div_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1 h2) hβ0) h3) h4) h5
  have hceil : (sourceSegments p L β y t ε : ℝ) < sourceSegmentReal p L β y t ε + 1 := by
    unfold sourceSegments
    exact Nat.ceil_lt_add_one hx0
  have hNp : 0 ≤ sourceMacroCount L p := by
    unfold sourceMacroCount
    positivity
  have heq5 : 0 ≤ eq5Bound p L β y t ε := by
    unfold eq5Bound
    have h1 : (0 : ℝ) ≤ (5 : ℝ) ^ (2 * p) := by positivity
    have h2 : (0 : ℝ) ≤ L ^ (2 + 1 / (p : ℝ)) := Real.rpow_nonneg hLpos.le _
    have h3 : (0 : ℝ) ≤ y ^ (1 / (2 * (p : ℝ))) := Real.rpow_nonneg hy _
    have h4 : (0 : ℝ) ≤ t ^ (1 + 1 / (2 * (p : ℝ))) := Real.rpow_nonneg ht _
    have h5 : (0 : ℝ) ≤ ε ^ (1 / (2 * (p : ℝ))) := (Real.rpow_pos_of_pos hε _).le
    exact div_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1 h2) hβ0) h3) h4) h5
  calc sourceNumTerms p L β y t ε
      = (sourceSegments p L β y t ε : ℝ) * sourceMacroCount L p := rfl
    _ ≤ (sourceSegmentReal p L β y t ε + 1) * sourceMacroCount L p :=
        mul_le_mul_of_nonneg_right hceil.le hNp
    _ = sourceSegmentReal p L β y t ε * sourceMacroCount L p +
          sourceMacroCount L p := by ring
    _ = 10 * eq5Bound p L β y t ε + sourceMacroCount L p := by
        rw [sourceSegmentReal_mul_macro hp hLpos hβ0]
    _ ≤ 20 * eq5Bound p L β y t ε + sourceMacroCount L p := by
        linarith [heq5]

/-- **Eq. (5), clean form (arXiv:1512.03416v1, p. 2)**: in the regime where
Eq. (14) yields at least one segment (`1 ≤ sourceSegmentReal`, the paper's
`y t ≥ ε` regime), the total number of exponentials is
`N ≤ 20 · 5^{2p} L^{2+1/p} β y^{1/(2p)} t^{1+1/(2p)} / ε^{1/(2p)}`, i.e. the
paper's `N = O(5^{2p} L^{2+1/p} β y^{1/(2p)} t^{1+1/(2p)} / ε^{1/(2p)})` with
explicit constant `20`. -/
theorem sourceNumTerms_le_eq5_of_one_le {p : ℕ} (hp : 1 ≤ p) {L β y t ε : ℝ}
    (hL : 1 ≤ L) (hβ : 1 ≤ β) (hy : 0 ≤ y) (ht : 0 ≤ t) (hε : 0 < ε)
    (hx1 : 1 ≤ sourceSegmentReal p L β y t ε) :
    sourceNumTerms p L β y t ε ≤ 20 * eq5Bound p L β y t ε := by
  have hLpos : (0 : ℝ) < L := by linarith
  have hβ0 : (0 : ℝ) ≤ β := by linarith
  have hx0 : 0 ≤ sourceSegmentReal p L β y t ε := le_trans (by norm_num) hx1
  have hceil : (sourceSegments p L β y t ε : ℝ) < sourceSegmentReal p L β y t ε + 1 := by
    unfold sourceSegments
    exact Nat.ceil_lt_add_one hx0
  have hNp : 0 ≤ sourceMacroCount L p := by
    unfold sourceMacroCount
    positivity
  have hdouble : sourceSegmentReal p L β y t ε + 1 ≤ 2 * sourceSegmentReal p L β y t ε := by
    linarith
  calc sourceNumTerms p L β y t ε
      = (sourceSegments p L β y t ε : ℝ) * sourceMacroCount L p := rfl
    _ ≤ (sourceSegmentReal p L β y t ε + 1) * sourceMacroCount L p :=
        mul_le_mul_of_nonneg_right hceil.le hNp
    _ ≤ (2 * sourceSegmentReal p L β y t ε) * sourceMacroCount L p :=
        mul_le_mul_of_nonneg_right hdouble hNp
    _ = 2 * (sourceSegmentReal p L β y t ε * sourceMacroCount L p) := by ring
    _ = 2 * (10 * eq5Bound p L β y t ε) := by
        rw [sourceSegmentReal_mul_macro hp hLpos hβ0]
    _ = 20 * eq5Bound p L β y t ε := by ring

end Qatlib.Papers.TrotterSuzuki15.MainResults.SourceTermCount
