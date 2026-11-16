/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SourceForms.FullSpaceGapGeometry

@[expose] public section


/-! # Orthogonal Gibbs projection and quadratic lower bounds

All statements use complex vectors. The Gibbs vector is allowed to be
unnormalized, and its orthogonal complement is represented by the explicit
matrix `fullGibbsComplement` used by the positive damping map.
-/



namespace Qatlib.Concepts.GibbsSource.SourceForms

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder

variable {ι : Type*} [Fintype ι]

/-- Full Star Dot conj for the stated finite source data. -/
theorem fullStarDot_conj (z w : ι → ℂ) :
    star z ⬝ᵥ w = star (star w ⬝ᵥ z) := by
  simp only [dotProduct, Pi.star_apply, star_sum, star_mul, star_star]

/-- Full Hermitian star Dot for the stated finite source data. -/
theorem fullHermitian_starDot {M : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (z w : ι → ℂ) :
    star z ⬝ᵥ (M *ᵥ w) = star (M *ᵥ z) ⬝ᵥ w := by
  rw [star_mulVec, hM.eq, dotProduct_mulVec]

/-- Full Hermitian quadratic im for the stated finite source data. -/
theorem fullHermitian_quadratic_im {M : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (z : ι → ℂ) : (star z ⬝ᵥ (M *ᵥ z)).im = 0 := by
  have hs : star z ⬝ᵥ (M *ᵥ z) = star (star z ⬝ᵥ (M *ᵥ z)) :=
    (fullHermitian_starDot hM z z).trans (fullStarDot_conj (M *ᵥ z) z)
  have hi := congrArg Complex.im hs
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

/-- Full Hermitian pos Semidef iff for the stated finite source data. -/
theorem fullHermitian_posSemidef_iff {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    M.PosSemidef ↔ ∀ z, 0 ≤ fullRayleigh M z := by
  refine ⟨fun h z => fullRayleigh_nonneg h z, fun h => ?_⟩
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hM
  intro z
  exact RCLike.nonneg_iff.mpr ⟨h z, fullHermitian_quadratic_im hM z⟩

/-- Full Rayleigh smul vector for the stated finite source data. -/
theorem fullRayleigh_smul_vector (c : ℂ) (M : Matrix ι ι ℂ) (z : ι → ℂ) :
    fullRayleigh M (c • z) = Complex.normSq c * fullRayleigh M z := by
  have hc : c * star c = (Complex.normSq c : ℂ) := Complex.mul_conj c
  have he : star (c • z) ⬝ᵥ (M *ᵥ (c • z)) =
      (Complex.normSq c : ℂ) * (star z ⬝ᵥ (M *ᵥ z)) := by
    simp only [star_smul, Matrix.mulVec_smul, smul_dotProduct,
      dotProduct_smul, smul_eq_mul]
    rw [← mul_assoc, hc]
  simp only [fullRayleigh, he, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

variable [DecidableEq ι]

/-- Full Gibbs Complement mul Vec for the stated finite source data. -/
theorem fullGibbsComplement_mulVec (g z : ι → ℂ) :
    fullGibbsComplement g *ᵥ z =
      z - ((star g ⬝ᵥ z) / (fullNormSq g : ℂ)) • g := by
  have ho : Matrix.vecMulVec g (star g) *ᵥ z = (star g ⬝ᵥ z) • g := by
    rw [Matrix.vecMulVec_mulVec]
    exact IsCentralScalar.op_smul_eq_smul _ _
  rw [fullGibbsComplement, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, ho, smul_smul, Complex.ofReal_inv]
  congr 2
  simp only [div_eq_mul_inv, mul_comm]

/-- Full Gibbs Complement is Hermitian for the stated finite source data. -/
theorem fullGibbsComplement_isHermitian (g : ι → ℂ) :
    (fullGibbsComplement g).IsHermitian := by
  apply Matrix.isHermitian_one.sub
  apply (Matrix.posSemidef_vecMulVec_self_star g).isHermitian.smul
  simp [IsSelfAdjoint]

/-- Full Gibbs Complement fix for the stated finite source data. -/
theorem fullGibbsComplement_fix (g z : ι → ℂ) (hz : star g ⬝ᵥ z = 0) :
    fullGibbsComplement g *ᵥ z = z := by
  rw [fullGibbsComplement_mulVec, hz, zero_div, zero_smul, sub_zero]

/-- Full Gibbs Complement gibbs for the stated finite source data. -/
theorem fullGibbsComplement_gibbs (g : ι → ℂ) (hg : g ≠ 0) :
    fullGibbsComplement g *ᵥ g = 0 := by
  have hn : (fullNormSq g : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (fullNormSq_pos g hg)
  rw [fullGibbsComplement_mulVec, fullStarDot_self_eq, div_self hn, one_smul, sub_self]

/-- Full Gibbs Complement orthogonal for the stated finite source data. -/
theorem fullGibbsComplement_orthogonal (g z : ι → ℂ) (hg : g ≠ 0) :
    star g ⬝ᵥ (fullGibbsComplement g *ᵥ z) = 0 := by
  have hn : (fullNormSq g : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (fullNormSq_pos g hg)
  rw [fullGibbsComplement_mulVec, dotProduct_sub, dotProduct_smul,
    fullStarDot_self_eq, smul_eq_mul, div_mul_cancel₀ _ hn, sub_self]

/-- Full Gibbs Complement idempotent mul Vec for the stated finite source data. -/
theorem fullGibbsComplement_idempotent_mulVec (g z : ι → ℂ) (hg : g ≠ 0) :
    fullGibbsComplement g *ᵥ (fullGibbsComplement g *ᵥ z) =
      fullGibbsComplement g *ᵥ z :=
  fullGibbsComplement_fix g _ (fullGibbsComplement_orthogonal g z hg)

/-- Full Rayleigh complement for the stated finite source data. -/
theorem fullRayleigh_complement (g z : ι → ℂ) :
    fullRayleigh (fullGibbsComplement g) z = fullVariance g z := by
  have hr : star z ⬝ᵥ (Matrix.vecMulVec g (star g) *ᵥ z) =
      (Complex.normSq (star g ⬝ᵥ z) : ℂ) := by
    rw [Matrix.vecMulVec_mulVec, IsCentralScalar.op_smul_eq_smul,
      dotProduct_smul, fullStarDot_conj z g, smul_eq_mul]
    exact Complex.mul_conj _
  rw [fullGibbsComplement, fullRayleigh_sub, fullRayleigh_one,
    fullRayleigh_real_smul]
  simp only [fullRayleigh, hr, Complex.ofReal_re, fullVariance, div_eq_mul_inv]
  ring

/-- Full Variance eq projected norm Sq for the stated finite source data. -/
theorem fullVariance_eq_projected_normSq (g z : ι → ℂ) (hg : g ≠ 0) :
    fullVariance g z = fullNormSq (fullGibbsComplement g *ᵥ z) := by
  have hs : star (fullGibbsComplement g *ᵥ z) =
      star z - star ((star g ⬝ᵥ z) / (fullNormSq g : ℂ)) • star g := by
    rw [fullGibbsComplement_mulVec, star_sub, star_smul]
  rw [← fullRayleigh_complement, fullNormSq, hs, sub_dotProduct,
    smul_dotProduct, fullGibbsComplement_orthogonal g z hg, smul_zero, sub_zero]
  rfl

/-- Full Variance nonneg for the stated finite source data. -/
theorem fullVariance_nonneg (g z : ι → ℂ) (hg : g ≠ 0) :
    0 ≤ fullVariance g z := by
  rw [fullVariance_eq_projected_normSq g z hg]
  exact fullNormSq_nonneg _

omit [DecidableEq ι] in
/-- Full Variance of orthogonal for the stated finite source data. -/
theorem fullVariance_of_orthogonal (g z : ι → ℂ) (hz : star g ⬝ᵥ z = 0) :
    fullVariance g z = fullNormSq z := by
  simp [fullVariance, hz]

/-- Full Variance eq zero iff for the stated finite source data. -/
theorem fullVariance_eq_zero_iff (g z : ι → ℂ) (hg : g ≠ 0) :
    fullVariance g z = 0 ↔ ∃ c : ℂ, z = c • g := by
  rw [fullVariance_eq_projected_normSq g z hg, fullNormSq_eq_zero_iff]
  constructor
  · intro hz
    refine ⟨(star g ⬝ᵥ z) / (fullNormSq g : ℂ), ?_⟩
    exact sub_eq_zero.mp ((fullGibbsComplement_mulVec g z).symm.trans hz)
  · rintro ⟨c, rfl⟩
    rw [Matrix.mulVec_smul, fullGibbsComplement_gibbs g hg, smul_zero]

/-- Full Rayleigh projected for the stated finite source data. -/
theorem fullRayleigh_projected {M : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (g z : ι → ℂ) (hMg : M *ᵥ g = 0) :
    fullRayleigh M (fullGibbsComplement g *ᵥ z) = fullRayleigh M z := by
  have ha : M *ᵥ (fullGibbsComplement g *ᵥ z) = M *ᵥ z := by
    rw [fullGibbsComplement_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul,
      hMg, smul_zero, sub_zero]
  have hb : star g ⬝ᵥ (M *ᵥ z) = 0 := by
    rw [fullHermitian_starDot hM g z, hMg]
    simp
  have hs : star (fullGibbsComplement g *ᵥ z) =
      star z - star ((star g ⬝ᵥ z) / (fullNormSq g : ℂ)) • star g := by
    rw [fullGibbsComplement_mulVec, star_sub, star_smul]
  rw [fullRayleigh, ha, hs, sub_dotProduct, smul_dotProduct, hb, smul_zero, sub_zero]
  rfl

/-- Full Lower Bound iff variance for the stated finite source data. -/
theorem fullLowerBound_iff_variance {M : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (g : ι → ℂ) (r : ℝ) :
    (M - (r : ℂ) • fullGibbsComplement g).PosSemidef ↔
      ∀ z, r * fullVariance g z ≤ fullRayleigh M z := by
  have hH : (M - (r : ℂ) • fullGibbsComplement g).IsHermitian :=
    hM.sub ((fullGibbsComplement_isHermitian g).smul (by simp [IsSelfAdjoint]))
  rw [fullHermitian_posSemidef_iff hH]
  simp only [fullRayleigh_sub, fullRayleigh_real_smul, fullRayleigh_complement,
    sub_nonneg]

end Qatlib.Concepts.GibbsSource.SourceForms
