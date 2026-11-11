/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# `SourceAugmentation` — the augmented system and the kernel of `G_t = Q_{b'} A_t`

Source: P. C. S. Costa, A. M. Dalzell, D. An, D. W. Berry,
*Constant Factor Analysis of Optimal Quantum Linear Solvers in Practice*,
arXiv:2604.22185v2 (fixed version), Section II B, Eqs. (7)–(9), and
Appendix A, Eqs. (A1)–(A6).

The Shortcut method enlarges `A ∈ ℂ^{n×n}` to a block-diagonal matrix
`A_t = diag(A, 1/t)` on the augmented space `ℂ^n ⊕ ℂ e_{m-1}` and sets
`b' = (b + e)/√2`, so that the *discriminant* `G_t = Q_{b'} A_t` annihilates
the augmented solution `x_t ∝ x + t·e`. Appendix A, Eq. (A2), observes
`G x = Q_b A x = 0`, and the text notes that "the kernel of `G_t` is the span
of `x_t` and the kernel of `A_t`".

We model the augmented space abstractly as one complex inner product space `E`
carrying an orthonormal augmentation vector `e`, with `A` mapping into `eᐧ⊥`
(the block-diagonal embedding). This reproduces the two summands exactly:
`ker A_t = ker A ∩ eᐧ⊥` and `ker G_t = span(x + t·e) ⊕ (ker A ∩ eᐧ⊥)`.
All statements below are exact; no approximation is used.
-/

set_option autoImplicit false
noncomputable section

open scoped ComplexInnerProductSpace

namespace Qatlib.Papers.LinSolverCF26.KernelReflect.SourceAugmentation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The orthogonal projection onto the complement of the augmentation
direction `e`: `Q_e u = u - ⟪e, u⟫ • e`. -/
def orthProj (e : E) : E →ₗ[ℂ] E where
  toFun u := u - ⟪e, u⟫ • e
  map_add' u v := by
    simp only [inner_add_right, add_smul, sub_eq_add_neg]
    abel
  map_smul' c u := by
    simp [inner_smul_right, smul_sub, smul_smul]

/-- Definitional unfolding of `orthProj`. -/
theorem orthProj_apply (e u : E) : orthProj e u = u - ⟪e, u⟫ • e := rfl

/-- The augmentation direction is killed by its own orthogonal projection. -/
theorem orthProj_self {e : E} (hee : ⟪e, e⟫ = 1) : orthProj e e = 0 := by
  rw [orthProj_apply, hee, one_smul, sub_self]

/-- A vector orthogonal to `e` is fixed by the projection. -/
theorem orthProj_of_orthogonal {e u : E} (hu : ⟪e, u⟫ = 0) : orthProj e u = u := by
  rw [orthProj_apply, hu, zero_smul, sub_zero]

/-- The image of the projection is orthogonal to `e`. -/
theorem inner_e_orthProj {e u : E} (hee : ⟪e, e⟫ = 1) : ⟪e, orthProj e u⟫ = 0 := by
  rw [orthProj_apply, inner_sub_right, inner_smul_right e e (⟪e, u⟫), hee, mul_one,
    sub_self]

/-- The enlarged matrix `A_t = diag(A, 1/t)`: it acts as `A` on the complement of
`e` and multiplies the `e`-component by `t⁻¹`. -/
def augMap (A : E →ₗ[ℂ] E) (t : ℝ) (e : E) : E →ₗ[ℂ] E :=
  A.comp (orthProj e) + ((t : ℂ)⁻¹) • (LinearMap.id - orthProj e)

/-- Unfolding of the enlarged matrix on a vector. -/
theorem augMap_apply (A : E →ₗ[ℂ] E) (t : ℝ) (e u : E) :
    augMap A t e u = A (orthProj e u) + ((t : ℂ)⁻¹) • (u - orthProj e u) := by
  simp [augMap, LinearMap.sub_apply]

/-- The normalized right-hand side `b' = (b + e)/√2`. -/
def bAug (b e : E) : E := ((Real.sqrt 2 : ℂ))⁻¹ • (b + e)

/-- The augmented solution direction `x_t ∝ x + t·e`. -/
def kernelVector (t : ℝ) (x e : E) : E := x + (t : ℂ) • e

/-- `b'` is a unit vector when `b` and `e` are orthonormal (Eq. (A2) context). -/
theorem norm_bAug {b e : E} (hb : ‖b‖ = 1) (he : ‖e‖ = 1) (hbe : ⟪e, b⟫ = 0) :
    ‖bAug b e‖ = 1 := by
  have hbe' : ⟪b, e⟫ = 0 := by
    rw [← inner_conj_symm, hbe]
    simp
  have hnorm2 : ‖b + e‖ ^ 2 = 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero b e hbe'
    rw [hb, he] at h
    norm_num at h
    nlinarith [h]
  have hnorm : ‖b + e‖ = Real.sqrt 2 := by
    rw [← Real.sqrt_sq (norm_nonneg (b + e)), hnorm2]
  have hsqrt_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  rw [bAug, norm_smul, hnorm]
  have hinv : ‖((Real.sqrt 2 : ℂ))⁻¹‖ = (Real.sqrt 2)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg 2)]
  rw [hinv]
  exact inv_mul_cancel₀ hsqrt_pos.ne'

/-- Eq. (A2) lifted to the augmented system: the kernel vector is mapped to
`√2 · b'`, hence lies in the kernel of `G_t = Q_{b'} A_t`. -/
theorem augMap_kernelVector {A : E →ₗ[ℂ] E} {t : ℝ} (ht : 0 < t) {x b e : E}
    (hAx : A x = b) (hxe : ⟪e, x⟫ = 0) (hee : ⟪e, e⟫ = 1) :
    augMap A t e (kernelVector t x e) = b + e := by
  have htne : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hinner : ⟪e, kernelVector t x e⟫ = (t : ℂ) := by
    rw [kernelVector, inner_add_right, hxe, zero_add, inner_smul_right e e (t : ℂ),
      hee, mul_one]
  have hproj : orthProj e (kernelVector t x e) = x := by
    rw [orthProj_apply, hinner, kernelVector]
    abel
  rw [augMap_apply, hproj, kernelVector]
  have hsub : x + (t : ℂ) • e - x = (t : ℂ) • e := by abel
  rw [hsub, smul_smul, hAx]
  have hcancel : (t : ℂ)⁻¹ * (t : ℂ) = 1 := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, inv_mul_cancel₀ ht.ne',
      Complex.ofReal_one]
  rw [hcancel, one_smul]

/-- `G_t` kills the kernel direction. -/
theorem augMap_kernelVector_eq_smul_bAug {A : E →ₗ[ℂ] E} {t : ℝ} (ht : 0 < t)
    {x b e : E} (hAx : A x = b) (hxe : ⟪e, x⟫ = 0) (hee : ⟪e, e⟫ = 1) :
    augMap A t e (kernelVector t x e) =
      (Real.sqrt 2 : ℂ) • bAug b e := by
  rw [augMap_kernelVector ht hAx hxe hee, bAug, smul_smul]
  have h2 : ((Real.sqrt 2 : ℂ)) ≠ 0 := by
    have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    exact_mod_cast hpos.ne'
  rw [mul_inv_cancel₀ h2, one_smul]

/-- The `e`-component of the enlarged matrix action. -/
theorem inner_e_augMap {A : E →ₗ[ℂ] E} {t : ℝ} {e : E}
    (hAorth : ∀ u, ⟪e, A u⟫ = 0) (hee : ⟪e, e⟫ = 1) (v : E) :
    ⟪e, augMap A t e v⟫ = (t : ℂ)⁻¹ * ⟪e, v⟫ := by
  rw [augMap_apply, inner_add_right, hAorth, zero_add,
    inner_smul_right e (v - orthProj e v) ((t : ℂ)⁻¹)]
  rw [inner_sub_right, inner_e_orthProj hee, sub_zero]

/-- `ker A_t = ker A ∩ eᐧ⊥` (the second summand of the kernel of `G_t`). -/
theorem kernel_augMap {A : E →ₗ[ℂ] E} {t : ℝ} (ht : 0 < t) {e : E}
    (hAorth : ∀ u, ⟪e, A u⟫ = 0) (hee : ⟪e, e⟫ = 1) (v : E) :
    augMap A t e v = 0 ↔ A (orthProj e v) = 0 ∧ ⟪e, v⟫ = 0 := by
  have htne : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  constructor
  · intro hv
    have hinner : (t : ℂ)⁻¹ * ⟪e, v⟫ = 0 := by
      rw [← inner_e_augMap hAorth hee v, hv, inner_zero_right]
    have hzero : ⟪e, v⟫ = 0 := by
      have hz := congrArg (fun z => (t : ℂ) * z) hinner
      beta_reduce at hz
      rw [mul_inv_cancel_left₀ htne, mul_zero] at hz
      exact hz
    have hA : A (orthProj e v) = 0 := by
      rw [augMap_apply] at hv
      have hsub : v - orthProj e v = 0 := by
        rw [orthProj_apply, hzero, zero_smul, sub_zero, sub_self]
      rw [hsub, smul_zero, add_zero] at hv
      exact hv
    exact ⟨hA, hzero⟩
  · rintro ⟨hA, hinner⟩
    rw [augMap_apply, hA]
    have hsub : v - orthProj e v = 0 := by
      rw [orthProj_apply, hinner, zero_smul, sub_zero, sub_self]
    rw [hsub, smul_zero, add_zero]

/-- **Kernel of the discriminant** (the paper's statement that "the kernel of
`G_t` is the span of `x_t` and the kernel of `A_t`"). Every vector the
discriminant kills is a complex multiple of the augmented solution `x + t·e`
plus a vector in `ker A` orthogonal to the augmentation direction. -/
theorem kernel_decomposition {A : E →ₗ[ℂ] E} {t : ℝ} (ht : 0 < t)
    {x b e : E} (hAx : A x = b) (hAorth : ∀ u, ⟪e, A u⟫ = 0)
    (hxe : ⟪e, x⟫ = 0) (hee : ⟪e, e⟫ = 1) :
    ∀ v : E, (∃ lam : ℂ, augMap A t e v = lam • bAug b e) ↔
      ∃ (lam : ℂ) (w : E), A w = 0 ∧ ⟪e, w⟫ = 0 ∧
        v = lam • kernelVector t x e + w := by
  intro v
  have htne : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hbe : ⟪e, b⟫ = 0 := by rw [← hAx, hAorth]
  constructor
  · rintro ⟨lam, hlam⟩
    set μ : ℂ := lam * ((Real.sqrt 2 : ℂ))⁻¹ with hμ
    have hlam' : augMap A t e v = μ • (b + e) := by
      rw [hlam, bAug, smul_smul, hμ]
    have hinner : (t : ℂ)⁻¹ * ⟪e, v⟫ = μ := by
      have h1 := congrArg (fun z => ⟪e, z⟫) hlam'
      beta_reduce at h1
      rw [inner_e_augMap hAorth hee v, inner_smul_right e (b + e) μ,
        inner_add_right, hbe, hee] at h1
      simp only [zero_add, mul_one] at h1
      exact h1
    have hc : ⟪e, v⟫ = (t : ℂ) * μ := by
      calc ⟪e, v⟫ = (t : ℂ) * ((t : ℂ)⁻¹ * ⟪e, v⟫) := by
            rw [mul_inv_cancel_left₀ htne]
        _ = (t : ℂ) * μ := by rw [hinner]
    have hApx : A (orthProj e v) = μ • b := by
      rw [augMap_apply] at hlam'
      have hsub : v - orthProj e v = ⟪e, v⟫ • e := by
        rw [orthProj_apply]
        abel
      rw [hsub, hc, smul_smul, ← mul_assoc, inv_mul_cancel₀ htne, one_mul,
        smul_add] at hlam'
      exact add_right_cancel hlam'
    refine ⟨μ, orthProj e v - μ • x, ?_, ?_, ?_⟩
    · rw [map_sub, hApx, map_smul, hAx, sub_self]
    · rw [inner_sub_right, inner_smul_right e x μ, inner_e_orthProj hee, hxe,
        mul_zero, sub_zero]
    · have hv : v = orthProj e v + ⟪e, v⟫ • e := by
        rw [orthProj_apply]
        abel
      calc v = orthProj e v + ⟪e, v⟫ • e := hv
        _ = orthProj e v + (μ * t) • e := by rw [hc, mul_comm (t : ℂ) μ]
        _ = μ • kernelVector t x e + (orthProj e v - μ • x) := by
              rw [kernelVector, smul_add, smul_smul]
              abel
  · rintro ⟨lam, w, hAw, hwe, rfl⟩
    have hprojw : orthProj e w = w := orthProj_of_orthogonal hwe
    have haugw : augMap A t e w = 0 := by
      rw [augMap_apply, hprojw]
      simp [hAw]
    have haugx : augMap A t e (kernelVector t x e) =
        (Real.sqrt 2 : ℂ) • bAug b e :=
      augMap_kernelVector_eq_smul_bAug ht hAx hxe hee
    refine ⟨lam * (Real.sqrt 2 : ℂ), ?_⟩
    rw [map_add, map_smul, haugx, haugw, add_zero, smul_smul]
