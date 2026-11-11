/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.MwEigenBranches
import Qatlib.Concepts.WalkSearch.Spectral.CompleteCSDecomposition

/-!
# Spectral mixtures of alternating measurement branches

Branch evolution is linear, and orthogonal clean eigenvectors remain orthogonal along each
common record. These facts yield `clean_record_mixture`, which expresses a clean state's branch
mass as a weighted sum of eigenvector record weights in a given spectral frame.

The mathematical background is developed in [MarriottWatrous2005].

## Main statements

* `record_cross_inner`: computes inner products after a common branch record.
* `record_mass_spectral_sum`: gives the branch-mass formula for an orthonormal eigenvector
  expansion.
* `clean_record_mixture`: expresses clean-state record mass through spectral coordinates.
* `clean_spectral_weights_sum_one`: shows that a normalized clean state's spectral weights form
  a probability distribution.

## References

* [Marriott and Watrous, 2005][MarriottWatrous2005]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.WalkSearch.Spectral

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open scoped Classical BigOperators
set_option linter.unusedSectionVars false

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- If `ψ` is fixed by `R` and `φ` has compressed eigenvalue `p`, applying `S` to both vectors
multiplies their inner product by `p`. -/
theorem same_cross_inner (R S : Matrix H H ℂ)
    (hR : IsOrthogonalProjector R) (hS : IsOrthogonalProjector S)
    (ψ φ : QState H) (p : ℝ) (hfix : R *ᵥ ψ = ψ)
    (heig : R *ᵥ (S *ᵥ φ) = (p : ℂ) • φ) :
    Inner (S *ᵥ ψ) (S *ᵥ φ) = (p : ℂ) * Inner ψ φ := by
  have hSs : Sᴴ = S := hS.2
  have hRs : Rᴴ = R := hR.2
  have hSS : Sᴴ * S = S := by rw [hSs, hS.1]
  calc
    _ = Inner ψ (S *ᵥ φ) := by
      rw [inner_mulVec_left_rect, Matrix.mulVec_mulVec, hSS]
    _ = Inner (R *ᵥ ψ) (S *ᵥ φ) := by rw [hfix]
    _ = Inner ψ (R *ᵥ (S *ᵥ φ)) := by rw [inner_mulVec_left_rect, hRs]
    _ = _ := by rw [heig, inner_smul_right]

/-- If `ψ` is fixed by `R` and `φ` has compressed eigenvalue `p`, applying `1 - S` to both
vectors multiplies their inner product by `1 - p`. -/
theorem different_cross_inner (R S : Matrix H H ℂ)
    (hR : IsOrthogonalProjector R) (hS : IsOrthogonalProjector S)
    (ψ φ : QState H) (p : ℝ) (hfix : R *ᵥ ψ = ψ)
    (heig : R *ᵥ (S *ᵥ φ) = (p : ℂ) • φ) :
    Inner ((1 - S) *ᵥ ψ) ((1 - S) *ᵥ φ) = (1 - (p : ℂ)) * Inner ψ φ := by
  have hT := isOrthogonalProjector_compl hS
  have hTs : (1 - S)ᴴ = 1 - S := hT.2
  have hRs : Rᴴ = R := hR.2
  have hTT : (1 - S)ᴴ * (1 - S) = 1 - S := by rw [hTs, hT.1]
  have hs : Inner ψ (S *ᵥ φ) = (p : ℂ) * Inner ψ φ := by
    calc
      _ = Inner (R *ᵥ ψ) (S *ᵥ φ) := by rw [hfix]
      _ = Inner ψ (R *ᵥ (S *ᵥ φ)) := by rw [inner_mulVec_left_rect, hRs]
      _ = _ := by rw [heig, inner_smul_right]
  rw [inner_mulVec_left_rect, Matrix.mulVec_mulVec, hTT,
    Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [show Inner ψ (φ - S *ᵥ φ) = Inner ψ φ - Inner ψ (S *ᵥ φ) by
    simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct_sub]]
  rw [hs]
  ring

/-- For clean eigenvectors with compressed eigenvalues `p` and `q`, a common branch record
scales their inner product by `recordWeight q record`. -/
theorem record_cross_inner (R S : Matrix H H ℂ)
    (hR : IsOrthogonalProjector R) (hS : IsOrthogonalProjector S)
    (ψ φ : QState H) (p q : ℝ) (hψ : R *ᵥ ψ = ψ) (hφ : R *ᵥ φ = φ)
    (heψ : R *ᵥ (S *ᵥ ψ) = (p : ℂ) • ψ)
    (heφ : R *ᵥ (S *ᵥ φ) = (q : ℂ) • φ) (record : List Bool) :
    Inner (branchState R S record ψ) (branchState R S record φ) =
      (recordWeight q record : ℂ) * Inner ψ φ := by
  induction record generalizing R S ψ φ with
  | nil => simp [branchState, recordWeight]
  | cons b rest ih =>
      cases b with
      | true =>
          obtain ⟨hψ', heψ'⟩ := same_invariant R S hS ψ p heψ
          obtain ⟨hφ', heφ'⟩ := same_invariant R S hS φ q heφ
          change Inner (branchState S R rest (S *ᵥ ψ))
            (branchState S R rest (S *ᵥ φ)) = _
          rw [ih S R hS hR (S *ᵥ ψ) (S *ᵥ φ) hψ' hφ' heψ' heφ',
            same_cross_inner R S hR hS ψ φ q hψ heφ]
          simp only [recordWeight, if_true, Complex.ofReal_mul]
          ring
      | false =>
          obtain ⟨hψ', heψ'⟩ := different_invariant R S hS ψ p hψ heψ
          obtain ⟨hφ', heφ'⟩ := different_invariant R S hS φ q hφ heφ
          change Inner (branchState (1 - S) (1 - R) rest ((1 - S) *ᵥ ψ))
            (branchState (1 - S) (1 - R) rest ((1 - S) *ᵥ φ)) = _
          rw [ih (1 - S) (1 - R) (isOrthogonalProjector_compl hS)
            (isOrthogonalProjector_compl hR) ((1 - S) *ᵥ ψ) ((1 - S) *ᵥ φ)
            hψ' hφ' heψ' heφ', different_cross_inner R S hR hS ψ φ q hψ heφ]
          simp only [recordWeight, Bool.false_eq_true, if_false, Complex.ofReal_mul,
            Complex.ofReal_sub, Complex.ofReal_one]
          ring

/-- Branch evolution distributes over any finite linear combination of input state vectors. -/
theorem branchState_sum {J : Type*} [Fintype J] (R S : Matrix H H ℂ)
    (v : J → QState H) (c : J → ℂ) (record : List Bool) :
    branchState R S record (∑ j, c j • v j) =
      ∑ j, c j • branchState R S record (v j) := by
  induction record generalizing R S v with
  | nil => rfl
  | cons b rest ih =>
      cases b <;>
        simp only [branchState, Matrix.mulVec_sum, Matrix.mulVec_smul] <;>
        apply ih

/-- For a family with diagonal Gram matrix of real entries `w`, the total mass of a linear
combination is the sum of squared coefficient norms times `w`. -/
theorem sum_norm_sq_diagonal_gram {J : Type*} [Fintype J]
    (v : J → QState H) (c : J → ℂ) (w : J → ℝ)
    (hv : ∀ j k, Inner (v j) (v k) = if j = k then (w j : ℂ) else 0) :
    MeasureProb (∑ j, c j • v j) Finset.univ = ∑ j, ‖c j‖ ^ 2 * w j := by
  change (∑ i, ‖(∑ j, c j • v j) i‖ ^ 2) = _
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_mul]
  rw [← inner_self]
  simp only [Qatlib.Foundations.PureStateMath.Inner, star_sum, star_smul, sum_dotProduct,
    dotProduct_sum, smul_dotProduct, dotProduct_smul, Finset.smul_sum]
  change (∑ j, ∑ k, c j * (star (c k) * Inner (v k) (v j))) = _
  simp_rw [hv]
  simp [mul_ite, ← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    RCLike.star_def]

/-- For an orthonormal family of clean compressed eigenvectors, each branch mass is the sum of
squared coefficient norms times the corresponding eigenvalue's record weight. -/
theorem record_mass_spectral_sum {J : Type*} [Fintype J]
    (R S : Matrix H H ℂ) (hR : IsOrthogonalProjector R) (hS : IsOrthogonalProjector S)
    (v : J → QState H) (c : J → ℂ) (t : J → ℝ)
    (hv : ∀ i j, Inner (v i) (v j) = if i = j then 1 else 0)
    (hfix : ∀ j, R *ᵥ v j = v j)
    (heig : ∀ j, R *ᵥ (S *ᵥ v j) = (t j : ℂ) • v j) (record : List Bool) :
    MeasureProb (branchState R S record (∑ j, c j • v j)) Finset.univ =
      ∑ j, ‖c j‖ ^ 2 * recordWeight (t j) record := by
  rw [branchState_sum]
  apply sum_norm_sq_diagonal_gram
  intro i j
  rw [record_cross_inner R S hR hS (v i) (v j) (t i) (t j)
    (hfix i) (hfix j) (heig i) (heig j), hv]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

/-- An isometric frame satisfying `A * Aᴴ = Q` and diagonalizing `Aᴴ * P * A` has orthonormal
columns fixed by `Q`, each satisfying the compressed eigenvector relation with its parameter
`t j`. -/
theorem spectral_frame_columns {J : Type*} [Fintype J] [DecidableEq J]
    (Q P : Matrix H H ℂ) (A : Matrix H J ℂ) (t : J → ℝ)
    (hA : IsIsometry A) (hAQ : A * Aᴴ = Q)
    (hdiag : Aᴴ * P * A = diagonal (fun j => (t j : ℂ))) :
    (∀ i j, Inner (fun h => A h i) (fun h => A h j) = if i = j then 1 else 0) ∧
    (∀ j, Q *ᵥ (fun h => A h j) = (fun h => A h j)) ∧
    (∀ j, Q *ᵥ (P *ᵥ (fun h => A h j)) = (t j : ℂ) • (fun h => A h j)) := by
  have hAA : Aᴴ * A = 1 := hA
  have hQA : Q * A = A := by
    rw [← hAQ, Matrix.mul_assoc, hAA, Matrix.mul_one]
  have hQPA : Q * (P * A) = A * diagonal (fun j => (t j : ℂ)) := by
    calc
      Q * (P * A) = (A * Aᴴ) * (P * A) := by rw [hAQ]
      _ = A * (Aᴴ * P * A) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hdiag]
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    have he := congrFun (congrFun hAA i) j
    simpa only [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Pi.star_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply] using! he
  · intro j
    exact congrArg (fun B : Matrix H J ℂ => fun h => B h j) hQA
  · intro j
    change (fun h => (Q * (P * A)) h j) = _
    rw [hQPA]
    funext h
    simp only [Matrix.mul_diagonal, Pi.smul_apply, smul_eq_mul]
    ring

/-- If `A * Aᴴ = Q`, every vector fixed by `Q` expands in the columns of `A` with coefficients
`Aᴴ *ᵥ ψ`. -/
theorem clean_frame_expansion {J : Type*} [Fintype J] [DecidableEq J]
    (Q : Matrix H H ℂ) (A : Matrix H J ℂ) (hAQ : A * Aᴴ = Q)
    (ψ : QState H) (hψ : Q *ᵥ ψ = ψ) :
    ψ = ∑ j, (Aᴴ *ᵥ ψ) j • (fun h => A h j) := by
  calc
    ψ = Q *ᵥ ψ := hψ.symm
    _ = A *ᵥ (Aᴴ *ᵥ ψ) := by rw [Matrix.mulVec_mulVec, hAQ]
    _ = _ := by
      funext h
      simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- In the stated spectral frame, a clean state's record mass is the sum of its squared spectral
coordinate norms times the component record weights. -/
theorem clean_record_mixture {J : Type*} [Fintype J] [DecidableEq J]
    (Q P : Matrix H H ℂ) (hQ : IsOrthogonalProjector Q) (hP : IsOrthogonalProjector P)
    (A : Matrix H J ℂ) (t : J → ℝ) (hA : IsIsometry A) (hAQ : A * Aᴴ = Q)
    (hdiag : Aᴴ * P * A = diagonal (fun j => (t j : ℂ)))
    (ψ : QState H) (hψ : Q *ᵥ ψ = ψ) (record : List Bool) :
    MeasureProb (branchState Q P record ψ) Finset.univ =
      ∑ j, ‖(Aᴴ *ᵥ ψ) j‖ ^ 2 * recordWeight (t j) record := by
  obtain ⟨hv, hfix, heig⟩ := spectral_frame_columns Q P A t hA hAQ hdiag
  have hexp := clean_frame_expansion Q A hAQ ψ hψ
  conv_lhs => rw [hexp]
  exact record_mass_spectral_sum Q P hQ hP (fun j h => A h j)
    (Aᴴ *ᵥ ψ) t (fun i j => by by_cases h : i = j <;> simpa [h] using! hv i j)
    hfix heig record

/-- The squared frame-coordinate norms of a normalized clean state are nonnegative and sum to
one. -/
theorem clean_spectral_weights_sum_one {J : Type*} [Fintype J] [DecidableEq J]
    (Q : Matrix H H ℂ) (A : Matrix H J ℂ) (hA : IsIsometry A) (hAQ : A * Aᴴ = Q)
    (ψ : QState H) (hψ : Q *ᵥ ψ = ψ) (hnψ : Normalized ψ) :
    (∀ j, 0 ≤ ‖(Aᴴ *ᵥ ψ) j‖ ^ 2) ∧ (∑ j, ‖(Aᴴ *ᵥ ψ) j‖ ^ 2) = 1 := by
  have hAA : Aᴴ * A = 1 := hA
  have hv : ∀ i j, Inner (fun h => A h i) (fun h => A h j) = if i = j then 1 else 0 := by
    intro i j
    have he := congrFun (congrFun hAA i) j
    simpa only [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Pi.star_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply] using! he
  have hsum := sum_norm_sq_diagonal_gram (fun j h => A h j) (Aᴴ *ᵥ ψ)
    (fun _ => 1) (fun i j => by simpa using! hv i j)
  simp only [mul_one] at hsum
  rw [← clean_frame_expansion Q A hAQ ψ hψ] at hsum
  have hm : MeasureProb ψ Finset.univ = 1 := hnψ
  rw [hm] at hsum
  exact ⟨fun j => sq_nonneg _, hsum.symm⟩

end Qatlib.Concepts.QueryComplexity.DegreeMethod
