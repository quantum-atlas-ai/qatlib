/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SourceForms.FullSpaceGapProjection
public import Qatlib.Concepts.GibbsSource.SourceForms.FullSpaceRayleighMinimum

@[expose] public section


/-! # The exact gap as optimal coercivity and an attained eigenvalue

Normalizing a nonzero projected vector gives the optimal quadratic lower
bound. The minimizing unit vector is then in the kernel of the PSD
remainder, so it is an actual eigenvector with eigenvalue equal to the
Rayleigh infimum. No eigenvalue enumeration or ordering is assumed.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra



namespace Qatlib.Concepts.GibbsSource.SourceForms

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder

variable {ι : Type*} [Fintype ι]

/-- Full Rayleigh Gap mul norm Sq le for the stated finite source data. -/
theorem fullRayleighGap_mul_normSq_le (M : Matrix ι ι ℂ) (g z : ι → ℂ)
    (hz : star g ⬝ᵥ z = 0) :
    fullRayleighGap M g * fullNormSq z ≤ fullRayleigh M z := by
  by_cases hz0 : z = 0
  · simp [hz0, fullRayleigh]
  have hn : 0 < fullNormSq z := fullNormSq_pos z hz0
  have hs : (Real.sqrt (fullNormSq z)) ^ 2 = fullNormSq z := Real.sq_sqrt hn.le
  have hs0 : Real.sqrt (fullNormSq z) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hn)
  let c : ℂ := ((Real.sqrt (fullNormSq z))⁻¹ : ℝ)
  have hscale : Complex.normSq c * fullNormSq z = 1 := by
    dsimp only [c]
    rw [Complex.normSq_ofReal]
    calc
      (Real.sqrt (fullNormSq z))⁻¹ * (Real.sqrt (fullNormSq z))⁻¹ * fullNormSq z =
          (Real.sqrt (fullNormSq z))⁻¹ * (Real.sqrt (fullNormSq z))⁻¹ *
            (Real.sqrt (fullNormSq z)) ^ 2 := by rw [hs]
      _ = 1 := by field_simp [hs0]
  have hu : c • z ∈ fullUnitOrthogonal g := by
    constructor
    · rw [fullNormSq_smul, hscale]
    · rw [dotProduct_smul, hz, smul_zero]
  have hle := fullRayleighGap_le M g (c • z) hu
  rw [fullRayleigh_smul_vector] at hle
  calc
    fullRayleighGap M g * fullNormSq z ≤
        (Complex.normSq c * fullRayleigh M z) * fullNormSq z :=
      mul_le_mul_of_nonneg_right hle hn.le
    _ = (Complex.normSq c * fullNormSq z) * fullRayleigh M z := by ring
    _ = fullRayleigh M z := by rw [hscale, one_mul]

variable [DecidableEq ι]

/-- Full Rayleigh Gap variance for the stated finite source data. -/
theorem fullRayleighGap_variance {M : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (g : ι → ℂ) (hg : g ≠ 0) (hMg : M *ᵥ g = 0) (z : ι → ℂ) :
    fullRayleighGap M g * fullVariance g z ≤ fullRayleigh M z := by
  have h := fullRayleighGap_mul_normSq_le M g (fullGibbsComplement g *ᵥ z)
    (fullGibbsComplement_orthogonal g z hg)
  rw [← fullVariance_eq_projected_normSq g z hg, fullRayleigh_projected hM g z hMg] at h
  exact h

/-- The exact infimum itself is a valid matrix lower bound. -/
theorem fullRayleighGap_lowerBound {M : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (g : ι → ℂ) (hg : g ≠ 0) (hMg : M *ᵥ g = 0) :
    (M - (fullRayleighGap M g : ℂ) • fullGibbsComplement g).PosSemidef :=
  (fullLowerBound_iff_variance hM g _).mpr (fullRayleighGap_variance hM g hg hMg)

/-- Every valid lower bound is bounded by the true minimum, provided the
unit Gibbs-orthogonal set is nonempty. -/
theorem fullLowerBound_le_gap {M : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (g : ι → ℂ) (r : ℝ) (hS : (fullUnitOrthogonal g).Nonempty)
    (hbound : (M - (r : ℂ) • fullGibbsComplement g).PosSemidef) :
    r ≤ fullRayleighGap M g := by
  obtain ⟨z, hz, he, _⟩ := fullRayleighGap_attained M g hS
  have h := (fullLowerBound_iff_variance hM g r).mp hbound z
  rw [fullVariance_of_orthogonal g z hz.2, hz.1, mul_one, ← he] at h
  exact h

omit [DecidableEq ι] in
/-- Full Unit Orthogonal ne zero for the stated finite source data. -/
theorem fullUnitOrthogonal_ne_zero (g z : ι → ℂ) (hz : z ∈ fullUnitOrthogonal g) :
    z ≠ 0 := by
  intro he
  have hn := hz.1
  rw [he, fullNormSq_zero] at hn
  norm_num at hn

/-- The minimum is a genuine eigenvalue with a nonzero unit eigenvector
in the Gibbs-orthogonal space. -/
theorem fullRayleighGap_eigenvector {M : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (g : ι → ℂ) (hg : g ≠ 0) (hMg : M *ᵥ g = 0)
    (hS : (fullUnitOrthogonal g).Nonempty) :
    ∃ z ∈ fullUnitOrthogonal g, M *ᵥ z = (fullRayleighGap M g : ℂ) • z := by
  obtain ⟨z, hz, he, _⟩ := fullRayleighGap_attained M g hS
  refine ⟨z, hz, ?_⟩
  have hbound := fullRayleighGap_lowerBound hM g hg hMg
  have hq : fullRayleigh
      (M - (fullRayleighGap M g : ℂ) • fullGibbsComplement g) z = 0 := by
    rw [fullRayleigh_sub, fullRayleigh_real_smul, fullRayleigh_complement,
      fullVariance_of_orthogonal g z hz.2, hz.1, mul_one, he, sub_self]
  have hk := (fullRayleigh_eq_zero_iff hbound z).mp hq
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, fullGibbsComplement_fix g z hz.2] at hk
  exact sub_eq_zero.mp hk

omit [DecidableEq ι] in
/-- Full Rayleigh Gap le eigenvalue for the stated finite source data. -/
theorem fullRayleighGap_le_eigenvalue {M : Matrix ι ι ℂ} (g z : ι → ℂ)
    (hz : z ≠ 0) (ho : star g ⬝ᵥ z = 0) (r : ℝ)
    (he : M *ᵥ z = (r : ℂ) • z) : fullRayleighGap M g ≤ r := by
  have hq : fullRayleigh M z = r * fullNormSq z := by
    simp only [fullRayleigh, he, dotProduct_smul, smul_eq_mul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      fullNormSq]
  have h := fullRayleighGap_mul_normSq_le M g z ho
  rw [hq] at h
  by_contra hnot
  have hp := mul_pos (sub_pos.mpr (lt_of_not_ge hnot)) (fullNormSq_pos z hz)
  nlinarith

/-- The same exact gap is a lower bound in the existing Hilbert--Schmidt
`FormGapAtLeast` interface, with no change of normalization. -/
theorem fullRayleighGap_formGap {D : ℕ} (L : Operator D →ₗ[ℂ] Operator D)
    (W : Operator D) (hL : (fullOpMatrix L).IsHermitian)
    (hW : fullVec W ≠ 0) (hLW : fullOpMatrix L *ᵥ fullVec W = 0) :
    FormGapAtLeast (fun X => (hsInner X (L X)).re) W
      (fullRayleighGap (fullOpMatrix L) (fullVec W)) := by
  intro X
  change fullRayleighGap (fullOpMatrix L) (fullVec W) * hsVar W X ≤
    (hsInner X (L X)).re
  rw [← fullVariance_fullVec W X, ← fullRayleigh_fullOpMatrix L X]
  exact fullRayleighGap_variance hL (fullVec W) hW hLW (fullVec X)

end Qatlib.Concepts.GibbsSource.SourceForms
