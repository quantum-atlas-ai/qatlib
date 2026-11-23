/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-!
# Phase averages for a jointly diagonal real model

Paper version: **arXiv:1106.1445v8**, [Wilde2017], Lemma A.0.3, fixed PDF p. 740.
<https://arxiv.org/abs/1106.1445>

This is a deliberately restricted real-`EuclideanSpace` slice of Lemma A.0.3:
the two orthonormal families are additionally assumed to have orthogonal
cross-terms `⟪χ_i, ζ_j⟫ = 0` whenever `i ≠ j`.  Under that joint-orthogonality
restriction the phase choice `γ_j = δ_j = 1` reduces the averaged overlap to the
average of the diagonal overlaps.  The unrestricted complex phase-averaging
argument is not proved here.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Qatlib.Papers.QShannonWilde11.MainResults.Appendix

open scoped BigOperators InnerProductSpace RealInnerProductSpace

noncomputable section

/-- **Lemma A.0.3, restricted jointly diagonal real model** — [Wilde2017],
arXiv:1106.1445v8, fixed PDF p. 740.  Two orthonormal real Euclidean families with
orthogonal off-diagonal cross-inner-products have unit phases whose normalized
averages inherit the common diagonal-overlap lower bound.  The phases are real
sign phases; in this restricted model both may be chosen identically equal to one. -/
theorem exists_phase_average_overlap_joint_diagonal
    {n m : ℕ} (hn : 0 < n) (_hm : 0 < m) (ε : ℝ)
    (χ ζ : Fin n → EuclideanSpace ℝ (Fin m))
    (_hχ : Orthonormal ℝ χ) (_hζ : Orthonormal ℝ ζ)
    (hcross : ∀ i j, i ≠ j → ⟪χ i, ζ j⟫_ℝ = 0)
    (hdiag : ∀ i, 1 - ε ≤ ⟪χ i, ζ i⟫_ℝ) :
    ∃ γ δ : Fin n → ℝ,
      (∀ i, |γ i| = 1 ∧ |δ i| = 1) ∧
        1 - ε ≤
          ⟪(Real.sqrt n)⁻¹ • ∑ i, γ i • χ i,
            (Real.sqrt n)⁻¹ • ∑ i, δ i • ζ i⟫_ℝ := by
  refine ⟨fun _ => 1, fun _ => 1, fun _ => ⟨abs_one, abs_one⟩, ?_⟩
  have hinner :
      ⟪∑ i, χ i, ∑ j, ζ j⟫_ℝ = ∑ i, ⟪χ i, ζ i⟫_ℝ := by
    simp only [sum_inner, inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i
      (fun j _ hji => hcross j i hji)
      (fun hi => absurd (Finset.mem_univ i) hi)]
  have hpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnn : 0 ≤ (n : ℝ) := by exact_mod_cast hn.le
  have hcoef : ((Real.sqrt n)⁻¹ * (Real.sqrt n)⁻¹) = (n : ℝ)⁻¹ := by
    rw [← pow_two, inv_pow, Real.sq_sqrt hnn]
  simp only [one_smul]
  rw [real_inner_smul_left, real_inner_smul_right, hinner, ← mul_assoc, hcoef,
    ← div_eq_inv_mul, le_div_iff₀ hpos]
  have hleft : (1 - ε) * (n : ℝ) = ∑ _ : Fin n, (1 - ε) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
  rw [hleft]
  exact Finset.sum_le_sum fun i _ => hdiag i

end

end Qatlib.Papers.QShannonWilde11.MainResults.Appendix
