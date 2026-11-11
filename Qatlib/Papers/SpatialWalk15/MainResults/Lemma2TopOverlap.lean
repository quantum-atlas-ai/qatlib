/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.RankOneSpectralSearch

/-!
# Eigenvector overlap from rank-one concentration

This module relates the residual of an eigenvector under a rank-one perturbation to its overlap
with the projector state. It derives deterministic overlap bounds from a matrix norm bound and
an eigenvalue lower bound, supporting Lemma 2 of [ChakrabortyEtAl2016].

## Main statements

* `lemma2_top_overlap_identity`: exact residual decomposition in terms of the squared overlap.
* `lemma2_top_overlap_from_concentration`: squared overlap at least `1 - 2 * δ`.
* `lemma2_uniform_overlap_from_concentration`: specialization to the uniform state.

## References

* [Chakraborty et al., 2016][ChakrabortyEtAl2016]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.RankOneSpectralSearch.RankOneSpectralSearch
open Qatlib.Foundations.PureStateMath.BornBridge
open scoped Classical BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.SpatialWalk15.MainResults.Lemma2TopOverlap

variable {I : Type} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in

/-- The squared Euclidean norm of a scalar multiple of a state is the squared scalar norm times
the squared Euclidean norm of the state. -/
theorem norm_sq_smul_fromVec (a : ℂ) (v : QState I) :
    ‖toEuclidean_fromVec (a • v)‖ ^ 2 = ‖a‖ ^ 2 * ‖toEuclidean_fromVec v‖ ^ 2 := by
  have h : toEuclidean_fromVec (a • v) = a • toEuclidean_fromVec v := rfl
  rw [h, norm_smul, mul_pow]

omit [DecidableEq I] in

/-- For orthogonal states, the squared Euclidean norm of their sum equals the sum of their
squared Euclidean norms. -/
theorem norm_sq_add_fromVec (x y : QState I) (h : Inner x y = 0) :
    ‖toEuclidean_fromVec (x + y)‖ ^ 2 =
      ‖toEuclidean_fromVec x‖ ^ 2 + ‖toEuclidean_fromVec y‖ ^ 2 := by
  have hinner : inner ℂ (toEuclidean_fromVec x) (toEuclidean_fromVec y) = 0 := by
    rw [inner_euclidean_fromVec, h]
  have hsum : toEuclidean_fromVec (x + y) = toEuclidean_fromVec x + toEuclidean_fromVec y := rfl
  rw [hsum, norm_add_sq (𝕜 := ℂ), hinner]
  simp

/-- The inner product of two normalized states has norm at most one. -/
theorem norm_inner_le_one (s x : QState I) (hs : Normalized s) (hx : Normalized x) :
    ‖Inner s x‖ ≤ 1 := by
  let vs : EuclideanSpace ℂ I := toEuclidean_fromVec s
  let vx : EuclideanSpace ℂ I := toEuclidean_fromVec x
  have h : ‖inner ℂ vs vx‖ ≤ ‖vs‖ * ‖vx‖ := norm_inner_le_norm (𝕜 := ℂ) vs vx
  rw [inner_euclidean_fromVec, (normalized_iff_norm_toEuclidean_fromVec s).1 hs,
    (normalized_iff_norm_toEuclidean_fromVec x).1 hx, mul_one] at h
  exact h

omit [DecidableEq I] in

/-- For normalized `s` and a normalized eigenvector `x` of `M` with real eigenvalue `ℓ`, the
squared residual under `M - rankOneProjector s` is `(ℓ - p) ^ 2 + p * (1 - p)`, where `p =
‖Inner s x‖ ^ 2` [ChakrabortyEtAl2016]. -/
theorem lemma2_top_overlap_identity (M : Matrix I I ℂ) (s x : QState I) (ℓ : ℝ)
    (hs : Normalized s) (hx : Normalized x) (hℓ : M *ᵥ x = (ℓ : ℂ) • x) :
    ‖toEuclidean_fromVec ((M - rankOneProjector s) *ᵥ x)‖ ^ 2 =
      (ℓ - ‖Inner s x‖ ^ 2) ^ 2 + ‖Inner s x‖ ^ 2 * (1 - ‖Inner s x‖ ^ 2) := by
  set α : ℂ := Inner s x
  set p : ℝ := ‖α‖ ^ 2
  set y : QState I := s - (starRingEnd ℂ) α • x
  have hxs : Inner x s = (starRingEnd ℂ) α := by
    rw [← inner_conj_state]
    simp [α]
  have hxx : Inner x x = 1 := (normalized_iff_inner_self x).1 hx
  have hsnorm : ‖toEuclidean_fromVec s‖ ^ 2 = 1 := by
    rw [norm_toEuclidean_fromVec_sq, hs]
  have hxnorm : ‖toEuclidean_fromVec x‖ ^ 2 = 1 := by
    rw [norm_toEuclidean_fromVec_sq, hx]
  have hdecomp : s = (starRingEnd ℂ) α • x + y := by
    simp only [y]
    abel
  have horth : Inner x y = 0 := by
    rw [show y = s - (starRingEnd ℂ) α • x from rfl, inner_sub_state, inner_smul_state,
      hxs, hxx, mul_one]
    ring
  have hxm : ‖toEuclidean_fromVec ((starRingEnd ℂ) α • x)‖ ^ 2 = p := by
    rw [norm_sq_smul_fromVec, hxnorm, mul_one]
    simp [p]
  have hynorm : ‖toEuclidean_fromVec y‖ ^ 2 = 1 - p := by
    have horth2 : Inner ((starRingEnd ℂ) α • x) y = 0 := by
      rw [inner_smul_left_state, horth, mul_zero]
    have hpyth := norm_sq_add_fromVec ((starRingEnd ℂ) α • x) y horth2
    have hsum : ‖toEuclidean_fromVec s‖ ^ 2 =
        ‖toEuclidean_fromVec ((starRingEnd ℂ) α • x)‖ ^ 2 + ‖toEuclidean_fromVec y‖ ^ 2 := by
      rw [← hpyth, ← hdecomp]
    linarith [hsum, hxm, hsnorm]
  have hmc : α * (starRingEnd ℂ) α = (p : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hact : (M - rankOneProjector s) *ᵥ x = ((ℓ - p : ℝ) : ℂ) • x + (-α) • y := by
    rw [Matrix.sub_mulVec, hℓ, rankOneProjector_mulVec]
    have hsmul : α • s = (p : ℂ) • x + α • y := by
      conv_lhs => rw [hdecomp]
      rw [smul_add, smul_smul, hmc]
    rw [hsmul]
    ext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
    push_cast
    ring
  have horth' : Inner (((ℓ - p : ℝ) : ℂ) • x) ((-α) • y) = 0 := by
    rw [inner_smul_left_state, inner_smul_state, horth, mul_zero, mul_zero]
  have hsplit := norm_sq_add_fromVec (((ℓ - p : ℝ) : ℂ) • x) ((-α) • y) horth'
  rw [hact, hsplit, norm_sq_smul_fromVec, norm_sq_smul_fromVec, hxnorm, hynorm]
  have h1 : ‖((ℓ - p : ℝ) : ℂ)‖ ^ 2 = (ℓ - p) ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h2 : ‖(-α)‖ ^ 2 = p := by
    rw [norm_neg]
  rw [h1, h2]
  ring

/-- If `M` is within matrix norm `η ≤ δ` of the projector onto normalized `s`, a normalized
eigenvector of real eigenvalue at least `1 - δ` has squared overlap with `s` at least `1 - 2
* δ`, assuming `η ≥ 0` [ChakrabortyEtAl2016]. -/
theorem lemma2_top_overlap_from_concentration (M : Matrix I I ℂ) (s x : QState I)
    (ℓ δ η : ℝ) (hs : Normalized s) (hx : Normalized x)
    (hℓ : M *ᵥ x = (ℓ : ℂ) • x) (hη0 : 0 ≤ η)
    (hconc : ‖M - rankOneProjector s‖ ≤ η) (hηδ : η ≤ δ) (hlow : 1 - δ ≤ ℓ) :
    1 - 2 * δ ≤ ‖Inner s x‖ ^ 2 := by
  have hstab := operator_norm_overlap_stability M s x η ℓ hs hx hη0 hℓ hconc
  linarith

/-- Under the stated concentration bound and eigenvalue lower bound, the overlap norm of the
normalized eigenvector with normalized `s` is at least `1 - 2 * δ`. -/
theorem lemma2_top_overlap_amplitude (M : Matrix I I ℂ) (s x : QState I)
    (ℓ δ η : ℝ) (hs : Normalized s) (hx : Normalized x)
    (hℓ : M *ᵥ x = (ℓ : ℂ) • x) (hη0 : 0 ≤ η)
    (hconc : ‖M - rankOneProjector s‖ ≤ η) (hηδ : η ≤ δ) (hlow : 1 - δ ≤ ℓ) :
    1 - 2 * δ ≤ ‖Inner s x‖ := by
  have hsq := lemma2_top_overlap_from_concentration M s x ℓ δ η hs hx hℓ hη0 hconc hηδ hlow
  have hle := norm_inner_le_one s x hs hx
  have hnn := norm_nonneg (Inner s x)
  have hprod : ‖Inner s x‖ * (1 - ‖Inner s x‖) ≥ 0 := mul_nonneg hnn (by linarith)
  nlinarith [hsq, hprod]

/-- On a finite type of positive cardinality, a normalized eigenvector with real eigenvalue at
least `1 - δ` has squared overlap with the uniform state at least `1 - 2 * δ` when the
stated matrix norm bound by `η ≤ δ` holds. -/
theorem lemma2_uniform_overlap_from_concentration (M : Matrix I I ℂ) (x : QState I)
    (ℓ δ η : ℝ) [Nonempty I] (hcard : 0 < Fintype.card I) (hx : Normalized x)
    (hℓ : M *ᵥ x = (ℓ : ℂ) • x) (hη0 : 0 ≤ η)
    (hconc : ‖M - rankOneProjector (Uniform I)‖ ≤ η) (hηδ : η ≤ δ) (hlow : 1 - δ ≤ ℓ) :
    1 - 2 * δ ≤ ‖Inner (Uniform I) x‖ ^ 2 :=
  lemma2_top_overlap_from_concentration M (Uniform I) x ℓ δ η
    (normalized_uniform hcard) hx hℓ hη0 hconc hηδ hlow

end Qatlib.Papers.SpatialWalk15.MainResults.Lemma2TopOverlap
