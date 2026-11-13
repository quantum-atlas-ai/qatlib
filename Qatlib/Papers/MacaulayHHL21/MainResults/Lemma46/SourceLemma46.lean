/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Basic
import Qatlib.Concepts.CoherentSim.CoherentOAA.Pseudoinverse
import Qatlib.Papers.MacaulayHHL21.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Shortest vector within a complex affine hull via Gram pseudoinverses

This file formalizes Lemma 4.6 of [Ding et al., 2021][DingEtAl2021] (pp. 8–9, Eqs. (12)–(13)):
for `V ∈ ℂ^{n × k}` (`k > 0`) with Gram matrix `G = Vᴴ V` and all-ones vector `1⃗ ∈ ℂ^k`:

1. The complex affine hull `{V x : ∑ᵢ xᵢ = 1}` contains the origin if and only if `1⃗` does not
   lie in the column space of `G`.
2. The squared length `γ*` of the shortest vector in the affine hull equals
   `max {γ ∈ ℝ : G - γ 1⃗ 1⃗ᵀ ⪰ 0}`; furthermore, when `γ* ≠ 0`, one has
   `γ* = 1 / Re⟨1⃗, G⁺ 1⃗⟩` and the shortest vector is `V (G⁺ 1⃗ / Re⟨1⃗, G⁺ 1⃗⟩)`.

## Main statements

* `PSD`: positive-semidefiniteness `∀ z, 0 ≤ Re(zᴴ A z)` on `Matrix (Fin m) (Fin m) ℂ`.
* `lemma46_shortestVector`: affine-hull origin criterion, semidefinite maximization formula,
  and explicit Moore–Penrose minimizer (Lemma 4.6).

## References

* [Ding et al., 2021][DingEtAl2021]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset Matrix

namespace Qatlib.Papers.MacaulayHHL21.MainResults.Lemma46

open Qatlib.Papers.MacaulayHHL21.MainResults
open Qatlib.Concepts.CoherentSim.CoherentOAA

/-- Positive-semidefinite order `A ⪰ 0` for a square complex matrix: every quadratic form
`zᴴ A z` has nonnegative real part ([Ding et al., 2021][DingEtAl2021], p. 8). -/
def PSD {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  ∀ z : Fin m → ℂ, 0 ≤ (star z ⬝ᵥ (A *ᵥ z)).re

/-- Identity `star z ⬝ᵥ ((Vᴴ * V) *ᵥ w) = star (V *ᵥ z) ⬝ᵥ (V *ᵥ w)`. -/
private lemma gram_dotProduct {n k : ℕ} (V : Matrix (Fin n) (Fin k) ℂ)
    (z w : Fin k → ℂ) :
    star z ⬝ᵥ ((Vᴴ * V) *ᵥ w) = star (V *ᵥ z) ⬝ᵥ (V *ᵥ w) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose,
    star_star]

/-- Identity `star ((Vᴴ * V) *ᵥ z) ⬝ᵥ w = star (V *ᵥ z) ⬝ᵥ (V *ᵥ w)`. -/
private lemma gram_dotProduct_left {n k : ℕ} (V : Matrix (Fin n) (Fin k) ℂ)
    (z w : Fin k → ℂ) :
    star ((Vᴴ * V) *ᵥ z) ⬝ᵥ w = star (V *ᵥ z) ⬝ᵥ (V *ᵥ w) := by
  have hst : ∀ {m : ℕ} (a b : Fin m → ℂ), star (star a ⬝ᵥ b) = star b ⬝ᵥ a := by
    intro m a b
    simp [dotProduct, star_sum, mul_comm]
  calc star ((Vᴴ * V) *ᵥ z) ⬝ᵥ w
      = star (star w ⬝ᵥ ((Vᴴ * V) *ᵥ z)) := (hst w ((Vᴴ * V) *ᵥ z)).symm
    _ = star (star (V *ᵥ w) ⬝ᵥ (V *ᵥ z)) := by rw [gram_dotProduct V w z]
    _ = star (V *ᵥ z) ⬝ᵥ (V *ᵥ w) := hst (V *ᵥ w) (V *ᵥ z)

/-- Real part of the Gram quadratic form `star z ⬝ᵥ ((Vᴴ * V) *ᵥ z)` equals `l2NormSq (V *ᵥ z)`. -/
private lemma gram_quad_eq_l2NormSq {n k : ℕ} (V : Matrix (Fin n) (Fin k) ℂ)
    (z : Fin k → ℂ) :
    (star z ⬝ᵥ ((Vᴴ * V) *ᵥ z)).re = l2NormSq (V *ᵥ z) := by
  rw [gram_dotProduct]
  simp only [dotProduct, Pi.star_apply, Complex.re_sum, l2NormSq]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hmul : star ((V *ᵥ z) j) * (V *ᵥ z) j = ((‖(V *ᵥ z) j‖ ^ 2 : ℝ) : ℂ) := by
    rw [RCLike.star_def, Complex.conj_mul', Complex.ofReal_pow]
  rw [hmul, Complex.ofReal_re]

/-- If `(Vᴴ * V) *ᵥ z = 0`, then `V *ᵥ z = 0`. -/
private lemma mulVec_eq_zero_of_gram_mulVec_eq_zero {n k : ℕ} (V : Matrix (Fin n) (Fin k) ℂ)
    {z : Fin k → ℂ} (hz : (Vᴴ * V) *ᵥ z = 0) : V *ᵥ z = 0 := by
  have hsq : l2NormSq (V *ᵥ z) = 0 := by
    rw [← gram_quad_eq_l2NormSq, hz, dotProduct_zero, Complex.zero_re]
  ext j
  have hnonneg : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ ‖(V *ᵥ z) i‖ ^ 2 :=
    fun i _ => sq_nonneg _
  have hj0 : ‖(V *ᵥ z) j‖ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsq j (Finset.mem_univ j)
  have hnorm0 : ‖(V *ᵥ z) j‖ = 0 := sq_eq_zero_iff.mp hj0
  exact norm_eq_zero.mp hnorm0

/-- All-ones rank-one quadratic form `(star z ⬝ᵥ (ones *ᵥ z)).re = ‖∑ i, z i‖ ^ 2`. -/
private lemma ones_quad_re {k : ℕ} (z : Fin k → ℂ) :
    (star z ⬝ᵥ (Matrix.of (fun _ _ : Fin k => (1 : ℂ)) *ᵥ z)).re = ‖∑ i : Fin k, z i‖ ^ 2 := by
  have hmul : Matrix.of (fun _ _ : Fin k => (1 : ℂ)) *ᵥ z = fun _ => ∑ j : Fin k, z j := by
    ext i
    simp [Matrix.mulVec, dotProduct]
  rw [hmul]
  have hdot : star z ⬝ᵥ (fun _ : Fin k => ∑ j : Fin k, z j) =
      star (∑ i : Fin k, z i) * (∑ j : Fin k, z j) := by
    simp only [dotProduct, Pi.star_apply, ← Finset.sum_mul, star_sum]
  rw [hdot, RCLike.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

/-- **Lemma 4.6** ([Ding et al., 2021][DingEtAl2021], pp. 8–9, Eqs. (12)–(13)): the origin lies
in the complex affine hull of the columns of `V` iff `1⃗` is not in the column space of the Gram
matrix `G = Vᴴ V`; the squared length `γ*` of the shortest vector is the maximal `γ` with
`G - γ 1⃗ 1⃗ᵀ ⪰ 0`, and when nonzero it equals `1 / Re⟨1⃗, G⁺ 1⃗⟩` with shortest vector
`V (G⁺ 1⃗ / Re⟨1⃗, G⁺ 1⃗⟩)`. -/
theorem lemma46_shortestVector {n k : ℕ} (hk : 0 < k)
    (V : Matrix (Fin n) (Fin k) ℂ) :
    let G : Matrix (Fin k) (Fin k) ℂ := V.conjTranspose * V
    let ones : Matrix (Fin k) (Fin k) ℂ := Matrix.of (fun _ _ => 1)
    let one : Fin k → ℂ := fun _ => 1
    ((∃ x : Fin k → ℂ, (∑ i, x i) = 1 ∧ V *ᵥ x = 0) ↔ ¬ ∃ x : Fin k → ℂ, G *ᵥ x = one) ∧
    (∃ γstar : ℝ, 0 ≤ γstar ∧ PSD (G - γstar • ones) ∧
      (∀ γ : ℝ, PSD (G - γ • ones) → γ ≤ γstar) ∧
      (γstar ≠ 0 →
        γstar = 1 / (star one ⬝ᵥ (matrixPseudoinverse G *ᵥ one)).re ∧
        l2Norm (V *ᵥ (((star one ⬝ᵥ (matrixPseudoinverse G *ᵥ one)).re)⁻¹ : ℂ) •
          (matrixPseudoinverse G *ᵥ one)) ^ 2 = γstar)) := by
  intro G ones one
  have hG_herm : Gᴴ = G := by
    simp [G, Matrix.conjTranspose_mul]
  let P : Matrix (Fin k) (Fin k) ℂ := G * matrixPseudoinverse G
  have hP_herm : Pᴴ = P := mul_matrixPseudoinverse_adjoint G
  have hPG : P * G = G := mul_matrixPseudoinverse_mul G
  have hGP : G * P = G := by
    have h := congrArg Matrix.conjTranspose hPG
    rwa [Matrix.conjTranspose_mul, hG_herm, hP_herm] at h
  have hP_idem : P * P = P := by
    dsimp [P]
    rw [Matrix.mul_assoc G (matrixPseudoinverse G) (G * matrixPseudoinverse G),
      ← Matrix.mul_assoc (matrixPseudoinverse G) G (matrixPseudoinverse G),
      matrixPseudoinverse_mul_self G]
  have hiff : (∃ x : Fin k → ℂ, (∑ i, x i) = 1 ∧ V *ᵥ x = 0) ↔
      ¬ ∃ x : Fin k → ℂ, G *ᵥ x = one := by
    constructor
    · rintro ⟨x, hx_sum, hVx⟩ ⟨y, hy⟩
      have h1 : star x ⬝ᵥ one = 1 := by
        have hs : star x ⬝ᵥ one = star (∑ i : Fin k, x i) := by
          simp [one, dotProduct, star_sum]
        rw [hs, hx_sum, star_one]
      have h0 : star x ⬝ᵥ one = 0 := by
        rw [← hy]
        dsimp [G]
        rw [gram_dotProduct, hVx, star_zero, zero_dotProduct]
      exact one_ne_zero (h1.symm.trans h0)
    · intro hnot
      let z : Fin k → ℂ := (1 - P) *ᵥ one
      have hGz : G *ᵥ z = 0 := by
        dsimp [z]
        rw [Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, hGP, sub_self,
          Matrix.zero_mulVec]
      have hVz : V *ᵥ z = 0 := mulVec_eq_zero_of_gram_mulVec_eq_zero V hGz
      have hz_ne : z ≠ 0 := by
        intro hz0
        apply hnot
        refine ⟨matrixPseudoinverse G *ᵥ one, ?_⟩
        have hsub : one - P *ᵥ one = 0 := by
          simpa [z, Matrix.sub_mulVec, Matrix.one_mulVec] using hz0
        have heq : P *ᵥ one = one := (sub_eq_zero.mp hsub).symm
        simpa [P, Matrix.mulVec_mulVec] using heq
      have hQ_herm : (1 - P)ᴴ = 1 - P := by
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP_herm]
      have hQ_idem : (1 - P) * (1 - P) = 1 - P := by
        rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hP_idem, sub_self,
          sub_zero]
      have hsum_eq : ∑ i : Fin k, star (z i) = star z ⬝ᵥ z := by
        have hlhs : ∑ i : Fin k, star (z i) = star z ⬝ᵥ one := by
          simp [one, dotProduct]
        rw [hlhs]
        dsimp [z]
        calc star ((1 - P) *ᵥ one) ⬝ᵥ one
            = star one ⬝ᵥ ((1 - P)ᴴ *ᵥ one) := by
              rw [Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]
          _ = star one ⬝ᵥ (((1 - P) * (1 - P)) *ᵥ one) := by rw [hQ_herm, hQ_idem]
          _ = star ((1 - P) *ᵥ one) ⬝ᵥ ((1 - P) *ᵥ one) := by
              rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
                ← hQ_herm, Matrix.vecMul_conjTranspose, star_star, hQ_herm]
      have hzz_pos : 0 < (star z ⬝ᵥ z).re := by
        obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hz_ne
        have hre : (star z ⬝ᵥ z).re = ∑ i : Fin k, ‖z i‖ ^ 2 := by
          simp only [dotProduct, Pi.star_apply, Complex.re_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [RCLike.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
        rw [hre]
        exact Finset.sum_pos' (fun i _ => sq_nonneg _)
          ⟨i₀, Finset.mem_univ i₀, pow_pos (norm_pos_iff.mpr hi₀) 2⟩
      have hsum_ne : ∑ i : Fin k, z i ≠ 0 := by
        intro hs0
        have hst0 : ∑ i : Fin k, star (z i) = 0 := by
          rw [← star_sum, hs0, star_zero]
        rw [hst0] at hsum_eq
        -- `hsum_eq : 0 = star z ⬝ᵥ z`
        have hre0 := congrArg Complex.re hsum_eq
        simp only [Complex.zero_re] at hre0
        linarith
      refine ⟨(∑ i : Fin k, z i)⁻¹ • z, ?_, ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
        exact inv_mul_cancel₀ hsum_ne
      · rw [Matrix.mulVec_smul, hVz, smul_zero]
  refine ⟨hiff, ?_⟩
  have hquad_sub : ∀ (γ : ℝ) (z : Fin k → ℂ),
      (star z ⬝ᵥ ((G - γ • ones) *ᵥ z)).re =
        l2NormSq (V *ᵥ z) - γ * ‖∑ i : Fin k, z i‖ ^ 2 := by
    intro γ z
    have hsub : (G - γ • ones) *ᵥ z = G *ᵥ z - (γ : ℂ) • (ones *ᵥ z) := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec]
      ext i
      simp [Complex.real_smul]
    rw [hsub, dotProduct_sub, dotProduct_smul, smul_eq_mul, Complex.sub_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    dsimp [G, ones]
    rw [gram_quad_eq_l2NormSq, ones_quad_re]
  by_cases hcol : ∃ y : Fin k → ℂ, G *ᵥ y = one
  · obtain ⟨y₀, hy₀⟩ := hcol
    let u : Fin k → ℂ := matrixPseudoinverse G *ᵥ one
    have hGu : G *ᵥ u = one := by
      calc G *ᵥ u = P *ᵥ one := by simp [P, u, Matrix.mulVec_mulVec]
        _ = P *ᵥ (G *ᵥ y₀) := by rw [hy₀]
        _ = (P * G) *ᵥ y₀ := Matrix.mulVec_mulVec y₀ P G
        _ = one := by rw [hPG, hy₀]
    have hVu_ne : V *ᵥ u ≠ 0 := by
      intro h0
      have hGu0 : G *ᵥ u = 0 := by
        dsimp [G]
        rw [← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
      rw [hGu] at hGu0
      exact one_ne_zero (congrFun hGu0 ⟨0, hk⟩)
    let α : ℝ := l2NormSq (V *ᵥ u)
    have hα_pos : 0 < α := by
      obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hVu_ne
      exact Finset.sum_pos' (fun j _ => sq_nonneg _)
        ⟨j₀, Finset.mem_univ j₀, pow_pos (norm_pos_iff.mpr hj₀) 2⟩
    have hone_u_re : (star one ⬝ᵥ u).re = α := by
      calc (star one ⬝ᵥ u).re
          = (star (G *ᵥ u) ⬝ᵥ u).re := by rw [hGu]
        _ = (star u ⬝ᵥ (G *ᵥ u)).re := by
            have hd : star (G *ᵥ u) ⬝ᵥ u = star u ⬝ᵥ (G *ᵥ u) :=
              (gram_dotProduct_left V u u).trans (gram_dotProduct V u u).symm
            rw [hd]
        _ = α := gram_quad_eq_l2NormSq V u
    have hu_sum : ∑ i : Fin k, u i = (α : ℂ) := by
      have hs : ∑ i : Fin k, u i = star one ⬝ᵥ u := by
        simp [one, dotProduct]
      rw [hs, ← hGu]
      dsimp [G]
      rw [gram_dotProduct_left V u u]
      simp only [dotProduct, Pi.star_apply, α, l2NormSq, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [RCLike.star_def, Complex.conj_mul', Complex.ofReal_pow]
    refine ⟨1 / α, by positivity, ?_, ?_, ?_⟩
    · intro z
      rw [hquad_sub]
      have hz_sum : ∑ i : Fin k, z i = star (V *ᵥ u) ⬝ᵥ (V *ᵥ z) := by
        have hs : ∑ i : Fin k, z i = star one ⬝ᵥ z := by simp [one, dotProduct]
        rw [hs, ← hGu]
        exact gram_dotProduct_left V u z
      have hcs : ‖∑ i : Fin k, z i‖ ^ 2 ≤ α * l2NormSq (V *ᵥ z) := by
        rw [hz_sum]
        have htri : ‖star (V *ᵥ u) ⬝ᵥ (V *ᵥ z)‖ ≤
            ∑ j : Fin n, ‖(V *ᵥ u) j‖ * ‖(V *ᵥ z) j‖ := by
          calc ‖∑ j : Fin n, star ((V *ᵥ u) j) * (V *ᵥ z) j‖
              ≤ ∑ j : Fin n, ‖star ((V *ᵥ u) j) * (V *ᵥ z) j‖ := norm_sum_le _ _
            _ = ∑ j : Fin n, ‖(V *ᵥ u) j‖ * ‖(V *ᵥ z) j‖ := by
                refine Finset.sum_congr rfl fun j _ => ?_
                rw [norm_mul, norm_star]
        have hsq1 : ‖star (V *ᵥ u) ⬝ᵥ (V *ᵥ z)‖ ^ 2 ≤
            (∑ j : Fin n, ‖(V *ᵥ u) j‖ * ‖(V *ᵥ z) j‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) htri 2
        exact hsq1.trans (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
          (fun j => ‖(V *ᵥ u) j‖) (fun j => ‖(V *ᵥ z) j‖))
      have hdiv : 1 / α * ‖∑ i : Fin k, z i‖ ^ 2 ≤ l2NormSq (V *ᵥ z) := by
        rw [one_div_mul_eq_div, div_le_iff₀' hα_pos]
        exact hcs
      linarith
    · intro γ hpsd
      have hu_psd := hpsd u
      rw [hquad_sub, hu_sum, Complex.norm_real, Real.norm_of_nonneg hα_pos.le] at hu_psd
      -- `0 ≤ α - γ * α ^ 2`
      have hmul : γ * α ^ 2 ≤ 1 / α * α ^ 2 := by
        have h1 : 1 / α * α ^ 2 = α := by field_simp [hα_pos.ne']
        linarith
      exact le_of_mul_le_mul_right hmul (pow_pos hα_pos 2)
    · intro _
      refine ⟨by rw [hone_u_re], ?_⟩
      dsimp only [u] at hone_u_re ⊢
      rw [hone_u_re, ← Complex.ofReal_inv]
      have hsmul : V *ᵥ ((α⁻¹ : ℝ) : ℂ) • (matrixPseudoinverse G *ᵥ one) =
          ((α⁻¹ : ℝ) : ℂ) • (V *ᵥ (matrixPseudoinverse G *ᵥ one)) :=
        Matrix.mulVec_smul V ((α⁻¹ : ℝ) : ℂ) (matrixPseudoinverse G *ᵥ one)
      rw [hsmul]
      have hsq_nonneg : 0 ≤ l2NormSq (((α⁻¹ : ℝ) : ℂ) • (V *ᵥ (matrixPseudoinverse G *ᵥ one))) :=
        Finset.sum_nonneg fun j _ => sq_nonneg _
      unfold l2Norm
      rw [Real.sq_sqrt hsq_nonneg]
      have hscale : l2NormSq (((α⁻¹ : ℝ) : ℂ) • (V *ᵥ (matrixPseudoinverse G *ᵥ one))) =
          (α⁻¹) ^ 2 * α := by
        simp only [l2NormSq, Pi.smul_apply, norm_smul, Complex.norm_real,
          Real.norm_of_nonneg (inv_nonneg.mpr hα_pos.le), mul_pow, ← Finset.mul_sum]
        rfl
      rw [hscale]
      field_simp [hα_pos.ne']
  · obtain ⟨x₀, hx₀_sum, hVx₀⟩ := hiff.mpr hcol
    refine ⟨0, le_rfl, ?_, ?_, fun h0 => False.elim (h0 rfl)⟩
    · intro z
      rw [hquad_sub, zero_mul, sub_zero]
      exact Finset.sum_nonneg fun j _ => sq_nonneg _
    · intro γ hpsd
      have hx_psd := hpsd x₀
      rw [hquad_sub, hVx₀, hx₀_sum, norm_one, one_pow, mul_one] at hx_psd
      have h0 : l2NormSq (0 : Fin n → ℂ) = 0 := by simp [l2NormSq]
      linarith

end Qatlib.Papers.MacaulayHHL21.MainResults.Lemma46
