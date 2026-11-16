/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PPTMatrix.OperatorCones.ForMathlib.PositiveRankOneSubtraction

@[expose] public section




/-!
# Real subtraction coefficients and smaller steps

The sharp coefficient from `PositiveRankOneSubtraction` is strictly positive on
a nonzero range direction. Every smaller real coefficient preserves positivity;
every scalar coefficient preserves the old kernel and hence cannot raise rank.
These facts allow a common minimum coefficient for a matrix and its partial
transpose.
-/

open Matrix
open scoped ComplexOrder

namespace Qatlib.Foundations.PPTMatrix.OperatorCones

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The positive real sharp coefficient, with the usual inverse-zero convention. -/
noncomputable def rangeThreshold (A : Matrix n n ℂ) (w : n → ℂ) : ℝ :=
  ((star w ⬝ᵥ (A *ᵥ w)).re)⁻¹

omit [DecidableEq n] in
/-- Establishes `ofReal_rangeThreshold`: `(rangeThreshold A w : ℂ) = (star w ⬝ᵥ (A *ᵥ w))⁻¹`, for the stated parameters. -/
theorem ofReal_rangeThreshold {A : Matrix n n ℂ} (hA : A.PosSemidef) (w : n → ℂ) :
    (rangeThreshold A w : ℂ) = (star w ⬝ᵥ (A *ᵥ w))⁻¹ := by
  have hreal := Complex.eq_re_of_ofReal_le (r := 0)
    (z := star w ⬝ᵥ (A *ᵥ w)) (by simpa using hA.dotProduct_mulVec_nonneg w)
  rw [rangeThreshold, Complex.ofReal_inv, ← hreal]

omit [DecidableEq n] in
/-- Establishes `rangeThreshold_pos`: `0 < rangeThreshold A w`, for the stated parameters. -/
theorem rangeThreshold_pos {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (w : n → ℂ) (hw : A *ᵥ w ≠ 0) : 0 < rangeThreshold A w := by
  apply inv_pos.mpr
  have hqne : star w ⬝ᵥ (A *ᵥ w) ≠ 0 := by
    intro hq
    exact hw (hA.dotProduct_mulVec_zero_iff.mp hq)
  have hpos := lt_of_le_of_ne (hA.dotProduct_mulVec_nonneg w) (Ne.symm hqne)
  exact (Complex.pos_iff.mp hpos).1

omit [DecidableEq n] in
/-- Subtracting any scalar multiple along a range direction preserves the old kernel. -/
theorem ker_le_ker_sub_range_projector {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (w : n → ℂ) (c : ℂ) :
    A.mulVecLin.ker ≤ (A - c • vecMulVec (A *ᵥ w) (star (A *ᵥ w))).mulVecLin.ker := by
  intro z hz
  change A *ᵥ z = 0 at hz
  change (A - c • vecMulVec (A *ᵥ w) (star (A *ᵥ w))) *ᵥ z = 0
  have hdot : star (A *ᵥ w) ⬝ᵥ z = 0 := by
    rw [Matrix.star_mulVec, hA.isHermitian.eq, ← Matrix.dotProduct_mulVec, hz,
      dotProduct_zero]
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
    hz, hdot, op_smul_eq_smul, zero_smul, smul_zero, sub_zero]

omit [DecidableEq n] in
/-- No scalar subtraction in an actual range direction can increase rank. -/
theorem rank_sub_range_projector_le {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (w : n → ℂ) (c : ℂ) :
    (A - c • vecMulVec (A *ᵥ w) (star (A *ᵥ w))).rank ≤ A.rank := by
  have hdim := Submodule.finrank_mono (ker_le_ker_sub_range_projector hA w c)
  have hA' := A.mulVecLin.finrank_range_add_finrank_ker
  have hB' := (A - c • vecMulVec (A *ᵥ w) (star (A *ᵥ w))).mulVecLin.finrank_range_add_finrank_ker
  change Module.finrank ℂ (LinearMap.range
      (A - c • vecMulVec (A *ᵥ w) (star (A *ᵥ w))).mulVecLin) ≤
    Module.finrank ℂ (LinearMap.range A.mulVecLin)
  omega

/-- Every real coefficient at most the sharp threshold preserves positivity. -/
theorem posSemidef_sub_range_projector_of_le {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (w : n → ℂ) (s : ℝ) (hs : s ≤ rangeThreshold A w) :
    (A - (s : ℂ) • vecMulVec (A *ᵥ w) (star (A *ᵥ w))).PosSemidef := by
  have hsharp : (A - (rangeThreshold A w : ℂ) •
      vecMulVec (A *ᵥ w) (star (A *ᵥ w))).PosSemidef := by
    rw [ofReal_rangeThreshold hA]
    exact posSemidef_rangeSubtraction hA w
  have hadd := (Matrix.posSemidef_vecMulVec_self_star (A *ᵥ w)).smul
    (Complex.zero_le_real.mpr (sub_nonneg.mpr hs))
  have heq : A - (s : ℂ) • vecMulVec (A *ᵥ w) (star (A *ᵥ w)) =
      (A - (rangeThreshold A w : ℂ) • vecMulVec (A *ᵥ w) (star (A *ᵥ w))) +
        ((rangeThreshold A w - s : ℝ) : ℂ) • vecMulVec (A *ᵥ w) (star (A *ᵥ w)) := by
    rw [Complex.ofReal_sub, sub_smul]
    module
  rw [heq]
  exact hsharp.add hadd

/-- A nonzero vector in the actual matrix range admits a positive sharp
subtraction. Smaller coefficients preserve positivity, and rank never increases. -/
theorem exists_positive_subtraction_of_range {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {u : n → ℂ} (hu : u ≠ 0) (hrange : ∃ w, A *ᵥ w = u) :
    ∃ t : ℝ, 0 < t ∧
      (A - (t : ℂ) • vecMulVec u (star u)).PosSemidef ∧
      (A - (t : ℂ) • vecMulVec u (star u)).rank < A.rank ∧
      (∀ s : ℝ, s ≤ t → (A - (s : ℂ) • vecMulVec u (star u)).PosSemidef) ∧
      (∀ s : ℝ, (A - (s : ℂ) • vecMulVec u (star u)).rank ≤ A.rank) := by
  obtain ⟨w, hw⟩ := hrange
  have hAw : A *ᵥ w ≠ 0 := by simpa only [hw] using hu
  refine ⟨rangeThreshold A w, rangeThreshold_pos hA w hAw, ?_, ?_, ?_, ?_⟩
  · simpa only [hw] using posSemidef_sub_range_projector_of_le hA w
      (rangeThreshold A w) le_rfl
  · have h := rank_rangeSubtraction_lt hA w hAw
    unfold rangeSubtraction at h
    rw [← ofReal_rangeThreshold hA w] at h
    simpa only [hw] using h
  · intro s hs
    simpa only [hw] using posSemidef_sub_range_projector_of_le hA w s hs
  · intro s
    simpa only [hw] using rank_sub_range_projector_le hA w (s : ℂ)

end Qatlib.Foundations.PPTMatrix.OperatorCones
