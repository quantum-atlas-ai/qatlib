/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DoubleBracket22.MainResults.Model.DoubleBracketModel
import Qatlib.Papers.DoubleBracket22.MainResults.Algebra.CommutatorFormulas

set_option backward.isDefEq.respectTransparency false

/-!
# DoubleBracket22 — Lemma 7 (bounding canonical brackets)

Source: arXiv:2206.11772v4, Lemma 7, Eqs. (82)–(83), printed p. 25.

The paper's Appendix A works with *unitarily invariant* norms (denoted `‖·‖`
without a subscript); the Hilbert–Schmidt / Frobenius norm is such a norm and is
the one instantiated here. With it:

* `‖[Δ(A), σ(B)]‖ ≤ 4‖A‖‖B‖` (Eq. (82)), using `‖Δ(A)‖ ≤ ‖A‖` (pinching) and
  `‖σ(B)‖ ≤ 2‖B‖` (triangle inequality);
* `‖[Δ(A),σ(A)] − [Δ(B),σ(B)]‖ ≤ 8 max{‖A‖,‖B‖}‖A−B‖` (Eq. (83)),
  via Lemma 6 (Eq. (76)) and linearity of `σ`.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.Frobenius BigOperators

namespace Qatlib.Papers.DoubleBracket22.MainResults.Algebra

open Qatlib.Papers.DoubleBracket22.MainResults.Model

/-- The Frobenius norm of the diagonal restriction is at most the norm of the
operator (the pinching inequality for the Hilbert–Schmidt norm; the diagonal
part only keeps a subset of the squared entries). -/
theorem norm_diagPart_le {D : ℕ} (A : Mat D) : ‖diagPart A‖ ≤ ‖A‖ := by
  rw [Matrix.frobenius_norm_def, Matrix.frobenius_norm_def,
      ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  apply Real.sqrt_le_sqrt
  have hdiag : ∀ i : Fin D,
      ∑ j, ‖diagPart A i j‖ ^ (2 : ℝ) = ‖A i i‖ ^ (2 : ℝ) := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp [diagPart, Matrix.diagonal_apply_eq]
    · intro j _ hji
      simp [diagPart, Matrix.diagonal_apply_ne _ (Ne.symm hji)]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  simp_rw [hdiag]
  apply Finset.sum_le_sum
  intro i _
  exact Finset.single_le_sum (f := fun j => ‖A i j‖ ^ (2 : ℝ))
    (fun j _ => by positivity) (Finset.mem_univ i)

/-- `‖σ(B)‖ ≤ 2‖B‖`: the off-diagonal part is `B` minus a diagonal contraction. -/
theorem norm_offDiag_le {D : ℕ} (B : Mat D) : ‖offDiag B‖ ≤ 2 * ‖B‖ := by
  unfold offDiag
  have h1 : ‖B - diagPart B‖ ≤ ‖B‖ + ‖diagPart B‖ := norm_sub_le _ _
  have h2 : ‖diagPart B‖ ≤ ‖B‖ := norm_diagPart_le B
  linarith

/-- Lemma 7, Eq. (82), p. 25. `‖[Δ(A), σ(B)]‖ ≤ 4‖A‖‖B‖`.

Paper proof (Eq. (84)): `‖[ΔA, σB]‖ ≤ 2‖ΔA‖‖σB‖ ≤ 2·‖A‖·2‖B‖`. -/
theorem lemma7_bracketBound {D : ℕ} (A B : Mat D) :
    ‖commMat (diagPart A) (offDiag B)‖ ≤ 4 * ‖A‖ * ‖B‖ := by
  unfold commMat
  calc ‖diagPart A * offDiag B - offDiag B * diagPart A‖
      ≤ ‖diagPart A * offDiag B‖ + ‖offDiag B * diagPart A‖ := norm_sub_le _ _
    _ ≤ ‖diagPart A‖ * ‖offDiag B‖ + ‖offDiag B‖ * ‖diagPart A‖ := by
        have h1 := norm_mul_le (diagPart A) (offDiag B)
        have h2 := norm_mul_le (offDiag B) (diagPart A)
        linarith
    _ ≤ ‖A‖ * (2 * ‖B‖) + (2 * ‖B‖) * ‖A‖ := by
        have hA := norm_diagPart_le A
        have hB := norm_offDiag_le B
        have hA0 : (0 : ℝ) ≤ ‖A‖ := norm_nonneg _
        have hB0 : (0 : ℝ) ≤ ‖B‖ := norm_nonneg _
        have hd0 : (0 : ℝ) ≤ ‖diagPart A‖ := norm_nonneg _
        have hs0 : (0 : ℝ) ≤ ‖offDiag B‖ := norm_nonneg _
        nlinarith [hA, hB, hA0, hB0, hd0, hs0]
    _ = 4 * ‖A‖ * ‖B‖ := by ring

/-- Linearity of `σ`: `σ(A) − σ(B) = σ(A − B)` (Eq. (85), p. 25). -/
theorem offDiag_sub {D : ℕ} (A B : Mat D) :
    offDiag A - offDiag B = offDiag (A - B) := by
  ext i j
  unfold offDiag diagPart
  by_cases h : i = j
  · subst h; simp [Matrix.diagonal_apply_eq]
  · simp [Matrix.diagonal_apply_ne _ h]

/-- Linearity of `Δ`: `Δ(A − B) = Δ(A) − Δ(B)`. -/
theorem diagPart_sub {D : ℕ} (A B : Mat D) :
    diagPart (A - B) = diagPart A - diagPart B := by
  unfold diagPart
  ext i j
  by_cases h : i = j
  · subst h; simp [Matrix.diagonal_apply_eq]
  · simp [Matrix.diagonal_apply_ne _ h]

/-- Lemma 7, Eq. (83), p. 25.
`‖[Δ(A),σ(A)] − [Δ(B),σ(B)]‖ ≤ 8 max{‖A‖,‖B‖}‖A−B‖`.

Follows the paper's Eqs. (86)–(88): Lemma 6 (76) splits the difference into
`[Δ(A−B), σ(A)] + [Δ(B), σ(A−B)]`, each bounded by (82). -/
theorem lemma7_bracketLipschitz {D : ℕ} (A B : Mat D) :
    ‖commMat (diagPart A) (offDiag A) - commMat (diagPart B) (offDiag B)‖ ≤
      8 * max ‖A‖ ‖B‖ * ‖A - B‖ := by
  have hid := lemma6_commutatorDiff (diagPart A) (offDiag A) (diagPart B) (offDiag B)
  rw [hid, ← diagPart_sub, offDiag_sub]
  calc ‖commMat (diagPart (A - B)) (offDiag A) + commMat (diagPart B) (offDiag (A - B))‖
      ≤ ‖commMat (diagPart (A - B)) (offDiag A)‖ +
          ‖commMat (diagPart B) (offDiag (A - B))‖ := norm_add_le _ _
    _ ≤ 4 * ‖A - B‖ * ‖A‖ + 4 * ‖B‖ * ‖A - B‖ := by
        have h1 := lemma7_bracketBound (A - B) A
        have h2 := lemma7_bracketBound B (A - B)
        linarith
    _ ≤ 8 * max ‖A‖ ‖B‖ * ‖A - B‖ := by
        have h1 : ‖A‖ ≤ max ‖A‖ ‖B‖ := le_max_left _ _
        have h2 : ‖B‖ ≤ max ‖A‖ ‖B‖ := le_max_right _ _
        have h3 : (0 : ℝ) ≤ ‖A - B‖ := norm_nonneg _
        have h4 : (0 : ℝ) ≤ max ‖A‖ ‖B‖ := le_trans (norm_nonneg _) h1
        have h5 : (0 : ℝ) ≤ ‖A‖ := norm_nonneg _
        have h6 : (0 : ℝ) ≤ ‖B‖ := norm_nonneg _
        nlinarith [h1, h2, h3, h4, h5, h6]

end Qatlib.Papers.DoubleBracket22.MainResults.Algebra
