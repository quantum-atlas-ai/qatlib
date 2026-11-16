/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SourceForms.SourceFrequencyKernel
public import Qatlib.Concepts.GibbsSource.SourceForms.FullSpacePositivity
public import Qatlib.Concepts.GibbsSource.SourceForms.FullSpaceGapNormalization

@[expose] public section


/-! # Exact Gibbs kernel of the complete source parent

The original proposals need only have scalar common commutant. No distinct
energy, distinct Bohr frequency, nonzero transition, or target kernel premise
is required. The zero source form first controls coherent frequency buckets;
their sum reconstructs each original proposal. Only this implication is used:
commuting with an unfiltered proposal alone need not kill its separate buckets.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds



namespace Qatlib.Concepts.GibbsSource.SourceForms

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder

variable {D : ℕ} {ι : Type*} [Fintype ι]

/-- Complex-valued quadratic identity for the existing weighted Gram,
before taking its real part. -/
theorem parentGramFamOp_hsInner_complex (ρ : Operator D) (w : ι → ι → ℝ)
    (A : ι → Operator D) (X : Operator D) :
    hsInner X (parentGramFamOp w ρ A X) = wplainForm w ρ A X := by
  classical
  simp only [parentGramFamOp_apply, hsInner_sum_right, hsInner_smul_right,
    ← hsInner_parentFactor_adjoint (fourthRoot_isHermitian ρ), wplainForm]

/-- The complete plain operator has exactly the original source forms as its
quadratic form, including all same-frequency cross terms and the physical half. -/
theorem fullParentOp_plain_hsInner (lam : Fin D → ℝ) (β : ℝ)
    (A : ι → Operator D) (X : Operator D) :
    hsInner X (fullParentOp lam β (fun _ => 1) A X) =
      ∑ P, ckgSourcePlainForm β (gibbsDiag lam β) (fullNu lam)
        (fullTransition (A P)) X := by
  classical
  rw [fullParentOp_apply, hsInner_sum_right]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [parentGramFamOp_hsInner_complex]
  have hw : fullWeight lam β (fun _ => 1) =
      fun a b => ckgSourceWeight β (fullNu lam a) (fullNu lam b) := by
    funext a b
    simp only [fullWeight, mul_one]
  rw [hw]
  rfl

/-- Full Gram Matrix plain rayleigh source for the stated finite source data. -/
theorem fullGramMatrix_plain_rayleigh_source (lam : Fin D → ℝ) (β : ℝ)
    (A : ι → Operator D) (z : FullCoord D → ℂ) :
    fullRayleigh (fullGramMatrix lam β (fun _ => 1) A) z =
      ∑ P, (ckgSourcePlainForm β (gibbsDiag lam β) (fullNu lam)
        (fullTransition (A P)) (fun i j => z (i, j))).re := by
  let X : Operator D := fun i j => z (i, j)
  have hquad := fullGramMatrix_rayleigh_eq_hsInner lam β (fun _ => 1) A z
  change star z ⬝ᵥ (fullGramMatrix lam β (fun _ => 1) A *ᵥ z) =
    hsInner X (fullParentOp lam β (fun _ => 1) A X) at hquad
  have hsource := fullParentOp_plain_hsInner lam β A X
  simpa only [fullRayleigh, Complex.re_sum, X] using! congrArg Complex.re (hquad.trans hsource)

omit [Fintype ι] in
/-- Scalar common commutant turns vanishing actual thermal factors into the
normalized Gibbs line. Positive definiteness is used only for this conjugation. -/
theorem parentFactors_eq_zero_imp_eq_smul_sqrt (ρ : Operator D) (hρ : ρ.PosDef)
    (A : ι → Operator D)
    (hscalar : ∀ Y : Operator D,
      (∀ P, Y * A P = A P * Y) → ∃ c : ℂ, Y = c • (1 : Operator D))
    (X : Operator D) (hfactor : ∀ P, parentFactor ρ (A P) X = 0) :
    ∃ c : ℂ, X = c • CFC.sqrt ρ := by
  let Y : Operator D := (fourthRoot ρ)⁻¹ * X * (fourthRoot ρ)⁻¹
  have hcomm : ∀ P, Y * A P = A P * Y := by
    intro P
    exact ((parentFactor_eq_zero_iff hρ).mp (hfactor P)).symm
  obtain ⟨c, hc⟩ := hscalar Y hcomm
  refine ⟨c, ?_⟩
  have hrestore : fourthRoot ρ * Y * fourthRoot ρ = X := by
    dsimp only [Y]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, fourthRoot_mul_inv hρ,
      Matrix.one_mul, Matrix.mul_assoc, fourthRoot_inv_mul hρ, Matrix.mul_one]
  calc
    X = fourthRoot ρ * Y * fourthRoot ρ := hrestore.symm
    _ = fourthRoot ρ * (c • (1 : Operator D)) * fourthRoot ρ := by rw [hc]
    _ = c • CFC.sqrt ρ := by
      rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, fourthRoot_mul_self]

/-- Exact complete-space kernel for every real finite spectrum and every
proposal family with scalar common commutant. The weights are the actual
CKG source weights, with no frequency-injectivity assumption. -/
theorem fullGramMatrix_plain_kernel [Nonempty (Fin D)]
    (lam : Fin D → ℝ) {β : ℝ} (hβ : 0 < β) (A : ι → Operator D)
    (hscalar : ∀ Y : Operator D,
      (∀ P, Y * A P = A P * Y) → ∃ c : ℂ, Y = c • (1 : Operator D))
    (z : FullCoord D → ℂ) :
    fullGramMatrix lam β (fun _ => 1) A *ᵥ z = 0 ↔
      ∃ c : ℂ, z = c • fullGibbsVector lam β := by
  classical
  constructor
  · intro hz
    let X : Operator D := fun i j => z (i, j)
    have hsum : (∑ P, (ckgSourcePlainForm β (gibbsDiag lam β) (fullNu lam)
        (fullTransition (A P)) X).re) = 0 := by
      rw [← fullGramMatrix_plain_rayleigh_source lam β A z]
      simp only [fullRayleigh, hz, dotProduct_zero, Complex.zero_re]
    have hzero : ∀ P, (ckgSourcePlainForm β (gibbsDiag lam β) (fullNu lam)
        (fullTransition (A P)) X).re = 0 := by
      have hn : ∀ P ∈ (Finset.univ : Finset ι),
          0 ≤ (ckgSourcePlainForm β (gibbsDiag lam β) (fullNu lam)
            (fullTransition (A P)) X).re :=
        fun P _ => fullSourcePlainForm_nonneg hβ _ _ _ _
      exact fun P => (Finset.sum_eq_zero_iff_of_nonneg hn).mp hsum P (Finset.mem_univ P)
    have hf : ∀ P, parentFactor (gibbsDiag lam β) (A P) X = 0 := by
      intro P
      have h := ckgSourcePlainForm_re_eq_zero_imp_parentFactor_sum hβ
        (gibbsDiag lam β) (fullNu lam) (fullTransition (A P)) X (hzero P)
      simpa only [fullTransition_sum] using h
    obtain ⟨c, hc⟩ := parentFactors_eq_zero_imp_eq_smul_sqrt (gibbsDiag lam β)
      (fullGibbsDiag_posDef lam β) A hscalar X hf
    have hs : (Real.sqrt (fullGibbsPartition lam β) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (fullGibbsPartition_pos lam β))
    refine ⟨c / (Real.sqrt (fullGibbsPartition lam β) : ℂ), ?_⟩
    have hm : X = (c / (Real.sqrt (fullGibbsPartition lam β) : ℂ)) •
        fullGibbsMatrix lam β := by
      rw [fullGibbsMatrix_eq_smul_sqrt, smul_smul, div_mul_cancel₀ c hs]
      exact hc
    change fullVec X = _
    rw [hm]
    rfl
  · rintro ⟨c, rfl⟩
    rw [Matrix.mulVec_smul, fullGramMatrix_gibbsVector_eq_zero, smul_zero]

end Qatlib.Concepts.GibbsSource.SourceForms
