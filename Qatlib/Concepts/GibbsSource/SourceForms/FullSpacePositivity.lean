/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SourceForms.FullSpaceGibbs

@[expose] public section


/-! # Positivity of the complete source-weighted plain parent

The existing Gaussian integral theorem permits repeated frequency labels.
We transport it by the actual source factors `exp(beta*nu/4)` and retain
the physical half in every proposal's family Gram. No frequency-injectivity
or positive-definiteness premise is introduced. All matrix-unit directions
and all same-frequency cross terms of the complete parent remain present.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds



namespace Qatlib.Concepts.GibbsSource.SourceForms

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder

variable {D : ℕ} {ι : Type*} [Fintype ι]

/-- The transported source-weighted Gram is nonnegative for an arbitrary
finite family. Equal frequencies are allowed, including identical labels. -/
theorem fullSourceWeightedGram_nonneg {β : ℝ} (hβ : 0 < β)
    (ν : ι → ℝ) (B : ι → Operator D) :
    0 ≤ ∑ a, ∑ b, ckgSourceWeight β (ν a) (ν b) * (hsInner (B a) (B b)).re := by
  classical
  let C : ι → Operator D := fun a => (Real.exp (β * ν a / 4) : ℂ) • B a
  have hscale (a b : ι) :
      (hsInner (C a) (C b)).re =
        Real.exp (β * ν a / 4) * Real.exp (β * ν b / 4) * (hsInner (B a) (B b)).re := by
    dsimp only [C]
    rw [hsInner_smul_right, hsInner_smul_left]
    exact re_ofReal_mul_star_ofReal_mul _ _ _
  have hterm (a b : ι) :
      ckgSourceWeight β (ν a) (ν b) * (hsInner (B a) (B b)).re =
        ckgWeight β (ν a) (ν b) * (hsInner (C a) (C b)).re := by
    rw [hscale, ckgSourceWeight_eq,
      show β * (ν a + ν b) / 4 = β * ν a / 4 + β * ν b / 4 from by ring,
      Real.exp_add]
    ring
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hterm a b]
  exact ckgWeightedGram_nonneg hβ ν C

/-- Source plain-form nonnegativity for every finite index type. This
version does not require the injective-frequency premise of the older API. -/
theorem fullSourcePlainForm_nonneg {β : ℝ} (hβ : 0 < β)
    (ρ : Operator D) (ν : ι → ℝ) (A : ι → Operator D) (X : Operator D) :
    0 ≤ (ckgSourcePlainForm β ρ ν A X).re := by
  rw [ckgSourcePlainForm, wplainForm_re_eq]
  exact div_nonneg
    (fullSourceWeightedGram_nonneg hβ ν (fun a => parentFactor ρ (A a) X)) (by norm_num)

/-- The actual complete plain parent has nonnegative Hilbert--Schmidt
Rayleigh form, with no restriction on repeated transition frequencies. -/
theorem fullParentOp_plain_nonneg {β : ℝ} (hβ : 0 < β)
    (lam : Fin D → ℝ) (A : ι → Operator D) (X : Operator D) :
    0 ≤ (hsInner X (fullParentOp lam β (fun _ => 1) A X)).re := by
  classical
  rw [fullParentOp_apply, hsInner_sum_right]
  have hre :
      (∑ P, hsInner X (parentGramFamOp (fullWeight lam β (fun _ => 1))
        (gibbsDiag lam β) (fullTransition (A P)) X)).re =
        ∑ P, (hsInner X (parentGramFamOp (fullWeight lam β (fun _ => 1))
          (gibbsDiag lam β) (fullTransition (A P)) X)).re :=
    map_sum complexReAddMonoidHom _ Finset.univ
  rw [hre]
  refine Finset.sum_nonneg fun P _ => ?_
  rw [← wplainForm_eq_parentGramFamOp (fourthRoot_isHermitian (gibbsDiag lam β))]
  have hw : fullWeight lam β (fun _ => 1) =
      fun a b => ckgSourceWeight β (fullNu lam a) (fullNu lam b) := by
    funext a b
    simp only [fullWeight, mul_one]
  rw [hw]
  exact fullSourcePlainForm_nonneg hβ (gibbsDiag lam β)
    (fullNu lam) (fullTransition (A P)) X

/-- The complete matrix quadratic form is the actual parent Rayleigh form
on the operator with these coordinates, for every complex vector. -/
theorem fullGramMatrix_rayleigh_eq_hsInner (lam : Fin D → ℝ) (β : ℝ)
    (kern : ℝ → ℝ) (A : ι → Operator D) (z : FullCoord D → ℂ) :
    star z ⬝ᵥ ((fullGramMatrix lam β kern A) *ᵥ z) =
      hsInner (fun i j => z (i, j))
        (fullParentOp lam β kern A (fun i j => z (i, j))) := by
  let X : Operator D := fun i j => z (i, j)
  change star z ⬝ᵥ ((fullGramMatrix lam β kern A) *ᵥ z) =
    hsInner X (fullParentOp lam β kern A X)
  have hvec : fullVec X = z := rfl
  have hact := fullGramMatrix_mulVec lam β kern A X
  rw [hvec] at hact
  rw [hact, hsInner_eq_sum X (fullParentOp lam β kern A X)]
  simp only [dotProduct, Pi.star_apply, fullVec, Fintype.sum_prod_type, X]

/-- Every complete complex coordinate vector has nonnegative real Rayleigh
form under the plain matrix; no direction is projected away. -/
theorem fullGramMatrix_plain_rayleigh_nonneg {β : ℝ} (hβ : 0 < β)
    (lam : Fin D → ℝ) (A : ι → Operator D) (z : FullCoord D → ℂ) :
    0 ≤ (star z ⬝ᵥ ((fullGramMatrix lam β (fun _ => 1) A) *ᵥ z)).re := by
  rw [fullGramMatrix_rayleigh_eq_hsInner]
  exact fullParentOp_plain_nonneg hβ lam A (fun i j => z (i, j))

/-- Full Conj Transpose sum for the stated finite source data. -/
private theorem fullConjTranspose_sum {κ : Type*} [Fintype κ]
    (f : κ → Matrix (FullCoord D) (FullCoord D) ℂ) :
    (∑ k, f k)ᴴ = ∑ k, (f k)ᴴ := by
  classical
  ext p q
  simp only [Matrix.conjTranspose_apply, Matrix.sum_apply]
  change (starRingEnd ℂ) (∑ k, f k q p) = ∑ k, (starRingEnd ℂ) (f k q p)
  exact map_sum (starRingEnd ℂ) _ Finset.univ

/-- Symmetry of the real transition weights gives Hermiticity of the
complete physical Gram. This is not a positivity premise. -/
theorem fullGramMatrix_isHermitian_of_weight_symm (lam : Fin D → ℝ) (β : ℝ)
    (kern : ℝ → ℝ) (A : ι → Operator D)
    (hw : ∀ a b : FullCoord D, fullWeight lam β kern a b = fullWeight lam β kern b a) :
    (fullGramMatrix lam β kern A).IsHermitian := by
  classical
  change (fullGramMatrix lam β kern A)ᴴ = fullGramMatrix lam β kern A
  simp only [fullGramMatrix, fullConjTranspose_sum, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hw b a]
  congr 1
  exact Complex.conj_ofReal _

/-- The source weight is symmetric, hence the complete plain matrix is
Hermitian without requiring distinct frequencies. -/
theorem fullGramMatrix_plain_isHermitian (lam : Fin D → ℝ) (β : ℝ)
    (A : ι → Operator D) :
    (fullGramMatrix lam β (fun _ => 1) A).IsHermitian := by
  apply fullGramMatrix_isHermitian_of_weight_symm lam β (fun _ => 1) A
  intro a b
  simp only [fullWeight, mul_one]
  exact ckgSourceWeight_symm β _ _

/-- Full Matrix rayleigh im for the stated finite source data. -/
private theorem fullMatrix_rayleigh_im {κ : Type*} [Fintype κ]
    {M : Matrix κ κ ℂ} (hM : M.IsHermitian) (z : κ → ℂ) :
    (star z ⬝ᵥ (M *ᵥ z)).im = 0 := by
  classical
  let q : ℂ := star z ⬝ᵥ (M *ᵥ z)
  have hexpand : q = ∑ i, ∑ j, star (z i) * M i j * z j := by
    simp only [q, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]
  have hstar : star q = q := by
    simp only [hexpand]
    change (starRingEnd ℂ) (∑ i, ∑ j, star (z i) * M i j * z j) =
      ∑ i, ∑ j, star (z i) * M i j * z j
    simp only [map_sum, map_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    change star (star (z j)) * star (M j i) * star (z i) = star (z i) * M i j * z j
    rw [star_star, hM.apply i j]
    ring
  have him : -q.im = q.im := by
    simpa only [Complex.star_def, Complex.conj_im] using congrArg Complex.im hstar
  change q.im = 0
  linarith

/-- The complete source plain matrix is genuinely positive semidefinite.
Hermiticity and the real Rayleigh estimate are both proved, not assumed. -/
theorem fullGramMatrix_plain_posSemidef {β : ℝ} (hβ : 0 < β)
    (lam : Fin D → ℝ) (A : ι → Operator D) :
    (fullGramMatrix lam β (fun _ => 1) A).PosSemidef := by
  have hM := fullGramMatrix_plain_isHermitian lam β A
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hM fun z => ?_
  have hre := fullGramMatrix_plain_rayleigh_nonneg hβ lam A z
  have him := fullMatrix_rayleigh_im hM z
  have hq : star z ⬝ᵥ ((fullGramMatrix lam β (fun _ => 1) A) *ᵥ z) =
      ((star z ⬝ᵥ ((fullGramMatrix lam β (fun _ => 1) A) *ᵥ z)).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using him
  rw [hq]
  exact Complex.zero_le_real.mpr hre


end Qatlib.Concepts.GibbsSource.SourceForms
