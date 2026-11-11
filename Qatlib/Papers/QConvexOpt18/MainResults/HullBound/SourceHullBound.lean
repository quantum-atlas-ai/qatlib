/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.InnerProductSpace.PiL2
import Qatlib.Papers.QConvexOpt18.MainResults.FiniteDiff.SourceFiniteDiff

set_option backward.isDefEq.respectTransparency false

/-!
# QConvexOpt18 Lemma 16: bounds on a symmetric generating set propagate to its hull

van Apeldoorn--Gilyén--Gribling--de Wolf, fixed arXiv:1809.00643v4
(accepted in Quantum 2019-12-03), Lemma 16.

Lemma 16. Let `S ⊆ ℝ^n` be such that `S = -S`, and let `conv(S)` denote the convex hull of `S`.
If `f : conv(S) → ℝ` is a convex function, `f 0 = 0`, and `|f s| ≤ δ` for all `s ∈ S`, then
`|f s'| ≤ δ` for all `s' ∈ conv(S)`.

The proof is the maximum principle for convex functions. The upper bound `f s' ≤ δ` is
`ConvexOn.exists_ge_of_mem_convexHull`: a convex function attains its maximum over a convex hull
on the generating set. The lower bound uses `f 0 = 0` and symmetry: `0` is the midpoint of `s'`
and `-s'`, both of which lie in `conv(S)` because `S = -S`, so convexity gives
`0 = f 0 ≤ (f s' + f (-s')) / 2`, and `f (-s') ≤ δ`.

`l1Norm_coordVec`, `l1Norm_smul`, `l1Norm_add_le` and `l1Norm_zero` record the elementary
`ℓ₁`-norm facts about the coordinate vectors of Definition 8 that later blocks reuse.

Boundary: an abstract convex-analysis statement about a function on a convex hull. It carries no
approximation, no probability and no query model; the finite-difference instantiation is
`SourceLinearApprox`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QConvexOpt18.MainResults

open scoped BigOperators

/-- Lemma 16 of arXiv:1809.00643v4. If `S` is symmetric (`S = -S`), `f` is convex on `conv S`,
`f 0 = 0`, and `|f|` is bounded by `δ` on `S`, then `|f|` is bounded by `δ` on `conv S`. -/
theorem source_convexHull_symmetric_bound {n : ℕ} (S : Set (Fin n → ℝ)) (hS : S = -S)
    (f : (Fin n → ℝ) → ℝ) (δ : ℝ) (hconv : ConvexOn ℝ (convexHull ℝ S) f)
    (h0 : f 0 = 0) (hbd : ∀ s ∈ S, |f s| ≤ δ) :
    ∀ s' ∈ convexHull ℝ S, |f s'| ≤ δ := by
  have hsymm : -convexHull ℝ S = convexHull ℝ S := by
    rw [← convexHull_neg, ← hS]
  intro s' hs'
  have hfun := hconv.2
  have hup : f s' ≤ δ := by
    obtain ⟨y, hy, hle⟩ :=
      ConvexOn.exists_ge_of_mem_convexHull (𝕜 := ℝ) (f := f) (s := convexHull ℝ S) (t := S)
        hconv (subset_convexHull ℝ S) hs'
    exact hle.trans (le_of_abs_le (hbd y hy))
  have hlow : -δ ≤ f s' := by
    have hnegmem : -s' ∈ convexHull ℝ S := by
      have h1 : -s' ∈ -convexHull ℝ S := by
        rw [Set.mem_neg]
        simpa using hs'
      rwa [hsymm] at h1
    obtain ⟨y, hy, hle⟩ :=
      ConvexOn.exists_ge_of_mem_convexHull (𝕜 := ℝ) (f := f) (s := convexHull ℝ S) (t := S)
        hconv (subset_convexHull ℝ S) hnegmem
    have hyδ : f y ≤ δ := le_of_abs_le (hbd y hy)
    have hzero : (1 / 2 : ℝ) • s' + (1 / 2 : ℝ) • (-s') = 0 := by
      rw [smul_neg]
      simp
    have hmid := hfun hs' hnegmem (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
    rw [hzero, smul_eq_mul, smul_eq_mul] at hmid
    rw [h0] at hmid
    linarith
  exact abs_le.mpr ⟨hlow, hup⟩

/-- The `ℓ₁` norm of a coordinate vector is one. -/
@[simp]
theorem l1Norm_coordVec {n : ℕ} (i : Fin n) : l1Norm (coordVec i) = 1 := by
  simp only [l1Norm, coordVec, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- Homogeneity of the `ℓ₁` norm. -/
theorem l1Norm_smul {n : ℕ} (c : ℝ) (v : Fin n → ℝ) : l1Norm (c • v) = |c| * l1Norm v := by
  simp only [l1Norm, Pi.smul_apply, smul_eq_mul, abs_mul, Finset.mul_sum]

/-- The `ℓ₁` norm satisfies the triangle inequality. -/
theorem l1Norm_add_le {n : ℕ} (v w : Fin n → ℝ) : l1Norm (v + w) ≤ l1Norm v + l1Norm w := by
  simp only [l1Norm, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => abs_add_le (v i) (w i)

/-- The `ℓ₁` norm of the origin vanishes. -/
@[simp]
theorem l1Norm_zero {n : ℕ} : l1Norm (0 : Fin n → ℝ) = 0 := by
  simp [l1Norm]

/-- The `ℓ₁` norm vanishes only at the origin. -/
theorem eq_zero_of_l1Norm_eq_zero {n : ℕ} {v : Fin n → ℝ} (hv : l1Norm v = 0) : v = 0 := by
  funext i
  have hterm : |v i| = 0 := by
    have hnonneg : ∀ j ∈ (Finset.univ : Finset (Fin n)), 0 ≤ |v j| := fun j _ => abs_nonneg _
    have := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hv i (Finset.mem_univ i)
    exact this
  simpa using abs_eq_zero.mp hterm

/-- The set `{± r eᵢ : i ∈ [n]}` whose convex hull is the `ℓ₁` ball of radius `r`. -/
def symCoordSet {n : ℕ} (r : ℝ) : Set (Fin n → ℝ) :=
  {v | ∃ i : Fin n, v = r • coordVec i ∨ v = -(r • coordVec i)}

/-- The generating set `{± r eᵢ}` is symmetric, as Lemma 16 requires. -/
theorem symCoordSet_eq_neg {n : ℕ} (r : ℝ) :
    symCoordSet (n := n) r = -symCoordSet (n := n) r := by
  ext v
  constructor
  · rintro ⟨i, hi | hi⟩
    · exact ⟨i, Or.inr (by simp [hi])⟩
    · exact ⟨i, Or.inl (by simp [hi])⟩
  · rintro ⟨i, hi | hi⟩
    · refine ⟨i, Or.inr ?_⟩
      exact neg_eq_iff_eq_neg.mp hi
    · refine ⟨i, Or.inl ?_⟩
      exact neg_inj.mp hi

end Qatlib.Papers.QConvexOpt18.MainResults
