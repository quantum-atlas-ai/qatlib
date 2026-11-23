/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Qatlib.Papers.CommuteTest05.MainResults.Lemma18Adversary

@[expose] public section

/-!
# The state-level increment of Lemma 18

Lemma 18 of [Itakura2005] bounds the change in the overlap of two coherent query states
when their inputs differ at one bit. This module treats the case in which the relative
oracle acts as a sign flip on a single complex coordinate. The AM–GM summation core is
available as `Qatlib.Papers.CommuteTest05.MainResults.Lemma18Adversary.lemma18_increment_bound`.

The finite-relation estimate controls the real part of the overlap sum in this phase-flip case
and takes the squared-coordinate mass bounds as hypotheses. The full oracle evolution and the
derivation of the mass bounds from relation degrees and one-bit neighbor injectivity remain open.

## Main statements

* `phaseFlipAt_overlap_change_le`: flipping one coordinate of a state changes its inner product
  by at most twice the product of the two coordinate norms.
* `lemma18_state_increment_bound`: the total real adversary-overlap change over a nonempty finite
  relation is bounded by `2 * |R| / sqrt(m * m')`.

## References

* [Itakura, 2005][Itakura2005]
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexConjugate ComplexInnerProductSpace

namespace Qatlib.Papers.CommuteTest05.RelationAdv

/-- Flip the sign of the `i`-th coordinate of a complex Euclidean state, leaving every other
coordinate unchanged. This is the coordinate action of a Boolean phase oracle. -/
def phaseFlipAt {ι : Type*} [DecidableEq ι] (i : ι)
    (u : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  u - (2 : ℂ) • EuclideanSpace.single i (u i)

/-- A single opposite phase flip changes an overlap by exactly minus twice one conjugate
coordinate product, hence by at most twice the product of the coordinate norms. -/
theorem phaseFlipAt_overlap_change_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (u v : EuclideanSpace ℂ ι) :
    ‖⟪phaseFlipAt i u, v⟫ - ⟪u, v⟫‖ ≤ 2 * ‖u i‖ * ‖v i‖ := by
  have hchange : ⟪phaseFlipAt i u, v⟫ - ⟪u, v⟫ = -((2 : ℂ) * (conj (u i) * v i)) := by
    rw [phaseFlipAt, inner_sub_left, inner_smul_left,
      EuclideanSpace.inner_single_left]
    simp only [map_ofNat]
    ring
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [hchange, norm_neg, Complex.norm_mul, Complex.norm_mul, h2, Complex.norm_conj]
  linarith

/-- The real part of the overlap sum after a relative phase flip at the selected coordinate
of each related pair. This is a phase-oracle specialization of the progress quantity in
[Itakura2005], Lemma 18. -/
def adversaryOverlapAfterFlip {ι X Y : Type*} [Fintype ι] [DecidableEq ι]
    (R : Finset (X × Y)) (d : X × Y → ι)
    (ψ : X → EuclideanSpace ℂ ι) (φ : Y → EuclideanSpace ℂ ι) : ℝ :=
  ∑ p ∈ R, (⟪phaseFlipAt (d p) (ψ p.1), φ p.2⟫ : ℂ).re

/-- The real adversary overlap before applying the phase oracle. -/
def adversaryOverlap {ι X Y : Type*} [Fintype ι]
    (R : Finset (X × Y))
    (ψ : X → EuclideanSpace ℂ ι) (φ : Y → EuclideanSpace ℂ ι) : ℝ :=
  ∑ p ∈ R, (⟪ψ p.1, φ p.2⟫ : ℂ).re

/-- Bound the real-part overlap change over a nonempty relation of normalized states under
single-coordinate relative phase flips. The selected squared-coordinate mass bounds are
assumed, and the positive parameters `m` and `m'` fix the bound for the whole relation. -/
theorem lemma18_state_increment_bound
    {ι X Y : Type*} [Fintype ι] [DecidableEq ι] [Nonempty X] [Nonempty Y]
    (R : Finset (X × Y)) (_hR : R.Nonempty) (d : X × Y → ι)
    (ψ : X → EuclideanSpace ℂ ι) (φ : Y → EuclideanSpace ℂ ι)
    {m m' : ℝ} (hm : 0 < m) (hm' : 0 < m')
    (_hψ : ∀ x, ‖ψ x‖ = 1) (_hφ : ∀ y, ‖φ y‖ = 1)
    (hmassX : ∑ p ∈ R, ‖ψ p.1 (d p)‖ ^ 2 ≤ (R.card : ℝ) / m)
    (hmassY : ∑ p ∈ R, ‖φ p.2 (d p)‖ ^ 2 ≤ (R.card : ℝ) / m') :
    |adversaryOverlapAfterFlip R d ψ φ - adversaryOverlap R ψ φ| ≤
      2 / Real.sqrt (m * m') * (R.card : ℝ) := by
  have hterm : ∀ p ∈ R,
      |(⟪phaseFlipAt (d p) (ψ p.1), φ p.2⟫ - ⟪ψ p.1, φ p.2⟫ : ℂ).re| ≤
        2 * ‖ψ p.1 (d p)‖ * ‖φ p.2 (d p)‖ := by
    intro p _
    exact Complex.abs_re_le_norm _ |>.trans
      (phaseFlipAt_overlap_change_le (d p) (ψ p.1) (φ p.2))
  have hsplit :
      (∑ p ∈ R, ((⟪phaseFlipAt (d p) (ψ p.1), φ p.2⟫ : ℂ).re -
          (⟪ψ p.1, φ p.2⟫ : ℂ).re)) =
        adversaryOverlapAfterFlip R d ψ φ - adversaryOverlap R ψ φ := by
    rw [adversaryOverlapAfterFlip, adversaryOverlap, ← Finset.sum_sub_distrib]
  have habs := Finset.abs_sum_le_sum_abs
    (fun p : X × Y => (⟪phaseFlipAt (d p) (ψ p.1), φ p.2⟫ -
      ⟪ψ p.1, φ p.2⟫ : ℂ).re) R
  simp only [Complex.sub_re] at habs
  rw [hsplit] at habs
  have hsum := Finset.sum_le_sum hterm
  have hproduct : (∑ p ∈ R, 2 * ‖ψ p.1 (d p)‖ * ‖φ p.2 (d p)‖) =
      2 * ∑ p ∈ R, ‖ψ p.1 (d p)‖ * ‖φ p.2 (d p)‖ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  have hscalar := Qatlib.Papers.CommuteTest05.MainResults.Lemma18Adversary.lemma18_increment_bound R d
    (fun x i => ‖ψ x i‖) (fun y i => ‖φ y i‖) hm hm'
    (fun p _ => ⟨Complex.norm_nonneg _, Complex.norm_nonneg _⟩)
    hmassX hmassY
  rw [hproduct] at hsum
  exact habs.trans (hsum.trans hscalar)

end Qatlib.Papers.CommuteTest05.RelationAdv
