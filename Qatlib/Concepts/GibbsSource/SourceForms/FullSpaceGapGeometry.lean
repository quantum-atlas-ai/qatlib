/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SourceForms.FullSpaceAssembly
public import Qatlib.Concepts.GibbsSource.FormAlgebra.ParentGap
public import Mathlib.Analysis.Matrix.Order

@[expose] public section


/-! # Finite complex Rayleigh geometry and the actual gap definition

The gap is the infimum of the quadratic form on the unit sphere orthogonal
to the specified Gibbs vector. Subsequent modules prove that this set is
compact, that the infimum is attained, and that exact Gibbs kernels make
the minimum strictly positive. No positive lower bound is used as a
definition of the exact gap.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds



namespace Qatlib.Concepts.GibbsSource.SourceForms

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder

variable {ι : Type*} [Fintype ι]

noncomputable def fullNormSq (z : ι → ℂ) : ℝ := (star z ⬝ᵥ z).re

noncomputable def fullRayleigh (M : Matrix ι ι ℂ) (z : ι → ℂ) : ℝ :=
  (star z ⬝ᵥ (M *ᵥ z)).re

noncomputable def fullVariance (g z : ι → ℂ) : ℝ :=
  fullNormSq z - Complex.normSq (star g ⬝ᵥ z) / fullNormSq g

noncomputable def fullGibbsComplement [DecidableEq ι] (g : ι → ℂ) : Matrix ι ι ℂ :=
  1 - (((fullNormSq g)⁻¹ : ℝ) : ℂ) • Matrix.vecMulVec g (star g)

def fullUnitOrthogonal (g : ι → ℂ) : Set (ι → ℂ) :=
  {z | fullNormSq z = 1 ∧ star g ⬝ᵥ z = 0}

noncomputable def fullRayleighGap (M : Matrix ι ι ℂ) (g : ι → ℂ) : ℝ :=
  sInf (fullRayleigh M '' fullUnitOrthogonal g)

/-- Full Norm Sq eq sum for the stated finite source data. -/
theorem fullNormSq_eq_sum (z : ι → ℂ) : fullNormSq z = ∑ i, Complex.normSq (z i) := by
  unfold fullNormSq dotProduct
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.star_apply, Complex.star_def]
  rw [mul_comm, Complex.mul_conj, Complex.ofReal_re]

/-- Full Star Dot self eq for the stated finite source data. -/
theorem fullStarDot_self_eq (z : ι → ℂ) : star z ⬝ᵥ z = (fullNormSq z : ℂ) := by
  rw [fullNormSq_eq_sum]
  push_cast
  unfold dotProduct
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.star_apply, Complex.star_def]
  rw [mul_comm, Complex.mul_conj]

/-- Full Norm Sq nonneg for the stated finite source data. -/
theorem fullNormSq_nonneg (z : ι → ℂ) : 0 ≤ fullNormSq z := by
  rw [fullNormSq_eq_sum]
  exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _

/-- The Hilbert--Schmidt coordinate norm of the zero vector is zero. -/
@[simp] theorem fullNormSq_zero : fullNormSq (0 : ι → ℂ) = 0 := by
  simp [fullNormSq, dotProduct]

/-- Full Norm Sq eq zero iff for the stated finite source data. -/
theorem fullNormSq_eq_zero_iff (z : ι → ℂ) : fullNormSq z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    rw [fullNormSq_eq_sum] at hz
    have he := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => Complex.normSq_nonneg (z i)).mp hz
    funext i
    exact Complex.normSq_eq_zero.mp (he i (Finset.mem_univ i))
  · rintro rfl
    exact fullNormSq_zero

/-- Full Norm Sq pos for the stated finite source data. -/
theorem fullNormSq_pos (z : ι → ℂ) (hz : z ≠ 0) : 0 < fullNormSq z := by
  by_contra hn
  exact hz ((fullNormSq_eq_zero_iff z).mp
    (le_antisymm (le_of_not_gt hn) (fullNormSq_nonneg z)))

/-- Full Norm Sq smul for the stated finite source data. -/
theorem fullNormSq_smul (c : ℂ) (z : ι → ℂ) :
    fullNormSq (c • z) = Complex.normSq c * fullNormSq z := by
  simp only [fullNormSq_eq_sum, Pi.smul_apply, smul_eq_mul,
    Complex.normSq_mul, Finset.mul_sum]

/-- Full Rayleigh nonneg for the stated finite source data. -/
theorem fullRayleigh_nonneg {M : Matrix ι ι ℂ} (hM : M.PosSemidef) (z : ι → ℂ) :
    0 ≤ fullRayleigh M z := hM.re_dotProduct_nonneg z

/-- Full Rayleigh eq zero iff for the stated finite source data. -/
theorem fullRayleigh_eq_zero_iff {M : Matrix ι ι ℂ} (hM : M.PosSemidef) (z : ι → ℂ) :
    fullRayleigh M z = 0 ↔ M *ᵥ z = 0 := by
  constructor
  · intro hz
    apply (hM.dotProduct_mulVec_zero_iff (x := z)).mp
    apply Complex.ext
    · exact hz
    · exact (RCLike.nonneg_iff.mp (hM.dotProduct_mulVec_nonneg z)).2
  · intro hz
    simp [fullRayleigh, hz]

/-- Full Rayleigh sub for the stated finite source data. -/
theorem fullRayleigh_sub (A B : Matrix ι ι ℂ) (z : ι → ℂ) :
    fullRayleigh (A - B) z = fullRayleigh A z - fullRayleigh B z := by
  simp only [fullRayleigh, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]

/-- Full Rayleigh real smul for the stated finite source data. -/
theorem fullRayleigh_real_smul (a : ℝ) (M : Matrix ι ι ℂ) (z : ι → ℂ) :
    fullRayleigh ((a : ℂ) • M) z = a * fullRayleigh M z := by
  simp [fullRayleigh, Matrix.smul_mulVec, dotProduct_smul, Complex.mul_re]

/-- Full Rayleigh one for the stated finite source data. -/
theorem fullRayleigh_one [DecidableEq ι] (z : ι → ℂ) :
    fullRayleigh (1 : Matrix ι ι ℂ) z = fullNormSq z := by
  simp only [fullRayleigh, Matrix.one_mulVec, fullNormSq]

/-- Full Vec star Dot for the stated finite source data. -/
theorem fullVec_starDot {D : ℕ} (W X : Operator D) :
    star (fullVec W) ⬝ᵥ fullVec X = hsInner W X := by
  simp only [dotProduct, fullVec, Pi.star_apply, Fintype.sum_prod_type, hsInner_eq_sum]

/-- Full Variance full Vec for the stated finite source data. -/
theorem fullVariance_fullVec {D : ℕ} (W X : Operator D) :
    fullVariance (fullVec W) (fullVec X) = hsVar W X := by
  simp only [fullVariance, fullNormSq, fullVec_starDot, hsVar]

/-- Full Rayleigh full Op Matrix for the stated finite source data. -/
theorem fullRayleigh_fullOpMatrix {D : ℕ} (L : Operator D →ₗ[ℂ] Operator D)
    (X : Operator D) :
    fullRayleigh (fullOpMatrix L) (fullVec X) = (hsInner X (L X)).re := by
  rw [fullRayleigh, fullOpMatrix_mulVec, fullVec_starDot]

end Qatlib.Concepts.GibbsSource.SourceForms
