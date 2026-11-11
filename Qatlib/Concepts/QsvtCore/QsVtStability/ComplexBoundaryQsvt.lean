/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.QsVtStability.InteriorComplexQsvt

/-!
# Boundary robustness of complex QSVT

This module constructs defect-square-root unitaries for Hermitian contractions and applies them
to rectangular Hermitian dilations. It proves square-root perturbation bounds for complex
phase-list singular responses, in the robustness setting of [GilyenSuLowWiebe2019].

For an odd phase list and an approximate block encoding, the actual compressed word has error
bounded by `4 * zs.length * √(ε / α)`, with query count equal to the list length.

## Main statements

* `complex_boundary_singular_response_stability`: Bound odd and even response perturbations on
  contractions.
* `complex_boundary_actual_encoded_word`: Transfer the bound to an actual encoded word and its
  query count.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.BlockEncoding.Postselection
set_option warningAsError false


open Qatlib.Concepts.WalkSearch.Spectral

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Qatlib.Concepts.QsvtCore.QsVtStability
open Matrix Polynomial Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

noncomputable local instance boundaryMatrixCStar {I : Type} [Fintype I] [DecidableEq I] :
    CStarAlgebra (Matrix I I ℂ) where

/-- A nonnegative real scalar maps to a nonnegative scalar matrix. -/
private theorem boundary_scalar_nonneg {I : Type} [Fintype I] [DecidableEq I]
    {r : ℝ} (hr : 0 ≤ r) : 0 ≤ algebraMap ℝ (Matrix I I ℂ) r := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact ((Matrix.PosSemidef.one : (1 : Matrix I I ℂ).PosSemidef).smul hr).nonneg

/-- The defect square root `√(1 - X * X)` used in the boundary unitary construction. -/
private noncomputable def boundaryDefect {I : Type} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) : Matrix I I ℂ := CFC.sqrt (1-X*X)

/-- For a Hermitian contraction `X`, the defect matrix `1 - X * X` is nonnegative. -/
private theorem boundaryDefect_positive {I : Type} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) (hX : X.IsHermitian) (hn : ‖X‖ ≤ 1) : 0 ≤ 1-X*X := by
  have h := CStarAlgebra.star_mul_le_algebraMap_norm_sq (a := X)
  rw [Matrix.star_eq_conjTranspose,hX] at h
  have hscalar : algebraMap ℝ (Matrix I I ℂ) (‖X‖^2) ≤ 1 := by
    rw [← map_one (algebraMap ℝ (Matrix I I ℂ)),← sub_nonneg,← map_sub]
    apply boundary_scalar_nonneg
    nlinarith [norm_nonneg X]
  exact sub_nonneg.mpr (h.trans hscalar)

/-- A matrix commutes with its defect square root. -/
private theorem boundaryDefect_commute {I : Type} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) : X * boundaryDefect X = boundaryDefect X * X := by
  have hc : Commute (1-X*X) X := by change (1-X*X)*X=X*(1-X*X); noncomm_ring
  exact (hc.cfcₙ_nnreal NNReal.sqrt).eq.symm

/-- The block matrix with diagonal blocks `X` and `-X` and both off-diagonal blocks equal to the
defect square root. -/
private noncomputable def boundaryUnitary {I : Type} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) : Matrix (I⊕I) (I⊕I) ℂ :=
  Matrix.fromBlocks X (boundaryDefect X) (boundaryDefect X) (-X)

/-- The boundary block construction is unitary for a Hermitian contraction. -/
private theorem boundaryUnitary_unitary {I : Type} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) (hX : X.IsHermitian) (hn : ‖X‖ ≤ 1) :
    boundaryUnitary X ∈ Matrix.unitaryGroup (I⊕I) ℂ := by
  have hS : (boundaryDefect X).IsHermitian := (CFC.sqrt_nonneg (1-X*X)).isSelfAdjoint
  have hx : Xᴴ=X := hX
  have hs : (boundaryDefect X)ᴴ=boundaryDefect X := hS
  have hsq : boundaryDefect X * boundaryDefect X = 1-X*X :=
    CFC.sqrt_mul_sqrt_self (1-X*X) (boundaryDefect_positive X hX hn)
  have hc := boundaryDefect_commute X
  rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose]
  simp only [boundaryUnitary,Matrix.fromBlocks_conjTranspose,Matrix.conjTranspose_neg,hx,hs,
    Matrix.fromBlocks_multiply,Matrix.mul_neg,Matrix.neg_mul,neg_neg,
    hsq,hc,add_sub_cancel,add_neg_cancel,sub_add_cancel]
  exact Matrix.fromBlocks_one

/-- The norm of the signed block diagonal matrix of a Hermitian `X` is at most `‖X‖`. -/
private theorem boundary_signed_diagonal_norm_le {I : Type} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) (hX : X.IsHermitian) :
    ‖Matrix.fromBlocks X 0 0 (-X)‖ ≤ ‖X‖ := by
  let J : Matrix (I⊕I) (I⊕I) ℂ := Matrix.fromBlocks 0 1 (-1) 0
  have hJ : J ∈ Matrix.unitaryGroup (I⊕I) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose]
    simp [J,Matrix.fromBlocks_conjTranspose,Matrix.fromBlocks_multiply,Matrix.fromBlocks_one]
  have he : Matrix.fromBlocks X 0 0 (-X) = J * hermitianDilation X := by
    have hx : Xᴴ=X := hX
    simp [J,hermitianDilation,Matrix.fromBlocks_multiply,hx]
  rw [he]
  exact (Matrix.l2_opNorm_mul _ _).trans (by
    rw [hermitianDilation_norm]
    exact mul_le_of_le_one_left (norm_nonneg X) (unitary_norm_le_one hJ))

/-- For contractions `X` and `Y`, their squared defect matrices differ by at most `2 * ‖X - Y‖`. -/
private theorem boundary_square_distance {I : Type} [Fintype I] [DecidableEq I]
    (X Y : Matrix I I ℂ) (hX : ‖X‖ ≤ 1) (hY : ‖Y‖ ≤ 1) :
    ‖(1-X*X)-(1-Y*Y)‖ ≤ 2*‖X-Y‖ := by
  have he : (1-X*X)-(1-Y*Y) = -(X*(X-Y)+(X-Y)*Y) := by noncomm_ring
  rw [he,norm_neg]
  calc
    _ ≤ ‖X*(X-Y)‖+‖(X-Y)*Y‖ := norm_add_le _ _
    _ ≤ ‖X‖*‖X-Y‖+‖X-Y‖*‖Y‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ 1*‖X-Y‖+‖X-Y‖*1 := add_le_add
      (mul_le_mul_of_nonneg_right hX (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hY (norm_nonneg _))
    _ = _ := by ring

/-- The boundary unitaries of Hermitian contractions differ by at most `4 * √‖X - Y‖`. -/
private theorem boundaryUnitary_distance {I : Type} [Fintype I] [DecidableEq I]
    (X Y : Matrix I I ℂ) (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (hnX : ‖X‖ ≤ 1) (hnY : ‖Y‖ ≤ 1) :
    ‖boundaryUnitary X-boundaryUnitary Y‖ ≤ 4*Real.sqrt ‖X-Y‖ := by
  have hS : (boundaryDefect X-boundaryDefect Y).IsHermitian :=
    ((CFC.sqrt_nonneg (1-X*X)).isSelfAdjoint.sub
      (CFC.sqrt_nonneg (1-Y*Y)).isSelfAdjoint).isHermitian
  have he : boundaryUnitary X-boundaryUnitary Y =
      Matrix.fromBlocks (X-Y) 0 0 (-(X-Y)) + hermitianDilation (boundaryDefect X-boundaryDefect Y) := by
    have hs : (boundaryDefect X-boundaryDefect Y)ᴴ=boundaryDefect X-boundaryDefect Y := hS
    unfold boundaryUnitary hermitianDilation
    rw [hs]
    ext i j
    cases i <;> cases j <;> simp
    ring
  have hboundary : ‖boundaryDefect X-boundaryDefect Y‖ ≤ Real.sqrt (2*‖X-Y‖) :=
    (positive_matrix_square_root_holder I (1-X*X) (1-Y*Y)
      (boundaryDefect_positive X hX hnX).posSemidef
      (boundaryDefect_positive Y hY hnY).posSemidef).trans
      (Real.sqrt_le_sqrt (boundary_square_distance X Y hnX hnY))
  have hδ : ‖X-Y‖ ≤ 2 := (norm_sub_le X Y).trans (by linarith)
  have hδ0 := norm_nonneg (X-Y)
  have hs := Real.sqrt_nonneg ‖X-Y‖
  have hs2 := Real.sq_sqrt hδ0
  have ht := Real.sqrt_nonneg (2*‖X-Y‖)
  have ht2 := Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ)≤2) hδ0)
  have hδs : ‖X-Y‖ ≤ 2*Real.sqrt ‖X-Y‖ := by nlinarith
  have hts : Real.sqrt (2*‖X-Y‖) ≤ 2*Real.sqrt ‖X-Y‖ := by nlinarith
  rw [he]
  calc
    _ ≤ ‖Matrix.fromBlocks (X-Y) 0 0 (-(X-Y))‖+
        ‖hermitianDilation (boundaryDefect X-boundaryDefect Y)‖ := norm_add_le _ _
    _ ≤ ‖X-Y‖+Real.sqrt (2*‖X-Y‖) := by
      rw [hermitianDilation_norm]
      exact add_le_add (boundary_signed_diagonal_norm_le (X-Y) (hX.sub hY)) hboundary
    _ ≤ _ := by linarith

/-- The Hermitian dilation of a rectangular matrix is Hermitian. -/
private theorem boundary_dilation_hermitian {I O : Type} [Fintype I] [Fintype O]
    (A : Matrix O I ℂ) : (hermitianDilation A).IsHermitian := by
  unfold Matrix.IsHermitian hermitianDilation
  simp [Matrix.fromBlocks_conjTranspose]

/-- The embedding into the first summand of the doubled Hermitian-dilation space. -/
private noncomputable def boundaryFirst {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] : Matrix ((O⊕I)⊕(O⊕I)) (O⊕I) ℂ :=
  (dilationLeft (I := O⊕I) (O := O⊕I))ᴴ
/-- The output frame obtained by composing the first-summand embedding with the output dilation
embedding. -/
private noncomputable def boundaryLeft {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] : Matrix ((O⊕I)⊕(O⊕I)) O ℂ :=
  boundaryFirst (I := I) (O := O) * (dilationLeft (I := I) (O := O))ᴴ
/-- The input frame obtained by composing the first-summand embedding with the input dilation
embedding. -/
private noncomputable def boundaryRight {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] : Matrix ((O⊕I)⊕(O⊕I)) I ℂ :=
  boundaryFirst (I := I) (O := O) * (dilationRight (I := I) (O := O))ᴴ

/-- A rectangular contraction is encoded by the boundary unitary of its Hermitian dilation and
the boundary frames. -/
private theorem boundary_projectedEncoding {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] (A : Matrix O I ℂ) (hn : ‖A‖ ≤ 1) :
    ProjectedUnitaryEncoding A (boundaryUnitary (hermitianDilation A)) boundaryLeft boundaryRight := by
  have hE : IsIsometry (boundaryFirst (I := I) (O := O)) :=
    dilationLeft_adjoint_isIsometry
  refine ⟨boundaryUnitary_unitary _ (boundary_dilation_hermitian A)
    (by simpa only [hermitianDilation_norm] using hn),
    Qatlib.Concepts.BlockEncoding.EncodingCore.IsIsometry.mul hE dilationLeft_adjoint_isIsometry,
    Qatlib.Concepts.BlockEncoding.EncodingCore.IsIsometry.mul hE dilationRight_adjoint_isIsometry, ?_⟩
  have he : compress (boundaryFirst (I := I) (O := O)) (boundaryUnitary (hermitianDilation A)) boundaryFirst =
      hermitianDilation A := by
    rw [boundaryFirst,compress_dilation_selectors11]
    rfl
  calc
    compress boundaryLeft (boundaryUnitary (hermitianDilation A)) boundaryRight =
      compress dilationLeftᴴ (compress boundaryFirst (boundaryUnitary (hermitianDilation A)) boundaryFirst)
        dilationRightᴴ := by
      unfold boundaryLeft boundaryRight compress
      rw [Matrix.conjTranspose_mul (boundaryFirst (I := I) (O := O))
        (dilationLeft (I := I) (O := O))ᴴ]
      simp only [Matrix.mul_assoc]
    _ = A := by rw [he,compress_dilation_selectors12]; rfl

/-- For contractions and unit phases, the odd or even singular response changes by at most `4 *
zs.length * √‖A - B‖`, according to list parity [GilyenSuLowWiebe2019]. -/
theorem complex_boundary_singular_response_stability :
    ∀ (I O : Type) [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
      (A B : Matrix O I ℂ) (base : ℂ) (zs : List ℂ),
      IsPhase base → (∀ z ∈ zs, IsPhase z) → ‖A‖ ≤ 1 → ‖B‖ ≤ 1 →
      (zs.length % 2 = 1 →
        ‖oddSingularTransform A (interiorResponse base zs) -
          oddSingularTransform B (interiorResponse base zs)‖ ≤ 4*zs.length*Real.sqrt ‖A-B‖) ∧
      (zs.length % 2 = 0 →
        ‖rightSingularTransform A (interiorResponse base zs) -
          rightSingularTransform B (interiorResponse base zs)‖ ≤ 4*zs.length*Real.sqrt ‖A-B‖) := by
  intro I O _ _ _ _ A B base zs hb hzs hA hB
  have hEA := boundary_projectedEncoding A hA
  have hEB := boundary_projectedEncoding B hB
  have hP := rangeProjector_isOrthogonalProjector hEA.right_isometry
  have hQ := rangeProjector_isOrthogonalProjector hEA.left_isometry
  have hdist : ‖boundaryUnitary (hermitianDilation A)-boundaryUnitary (hermitianDilation B)‖ ≤
      4*Real.sqrt ‖A-B‖ := by
    simpa only [hermitianDilation_sub_norm] using boundaryUnitary_distance
      (hermitianDilation A) (hermitianDilation B)
      (boundary_dilation_hermitian A) (boundary_dilation_hermitian B)
      (by simpa only [hermitianDilation_norm] using hA)
      (by simpa only [hermitianDilation_norm] using hB)
  have hrate : (zs.length : ℝ) *
      ‖boundaryUnitary (hermitianDilation A)-boundaryUnitary (hermitianDilation B)‖ ≤
        4*zs.length*Real.sqrt ‖A-B‖ := by
    exact (mul_le_mul_of_nonneg_left hdist (Nat.cast_nonneg _)).trans_eq (by ring)
  constructor
  · intro hodd
    change ‖oddSingularTransform A (fun x => (responseP base zs).eval (x : ℂ)) -
      oddSingularTransform B (fun x => (responseP base zs).eval (x : ℂ))‖ ≤ _
    rw [← qsvt_odd_eq_oddSingularTransform hEA base zs hodd,
      ← qsvt_odd_eq_oddSingularTransform hEB base zs hodd]
    exact (compress_phasedAlternating_oracle_error hEA.left_isometry hEA.right_isometry
      hEA.unitary hEB.unitary hP hQ hb zs hzs).trans hrate
  · intro heven
    change ‖rightSingularTransform A (fun x => (responseP base zs).eval (x : ℂ)) -
      rightSingularTransform B (fun x => (responseP base zs).eval (x : ℂ))‖ ≤ _
    rw [← qsvt_even_right_eq_rightSingularTransform hEA base zs heven,
      ← qsvt_even_right_eq_rightSingularTransform hEB base zs heven]
    have h := compress_phasedAlternating_oracle_error hEA.right_isometry hEA.right_isometry
      (adjoint_unitary hEA.unitary) (adjoint_unitary hEB.unitary) hQ hP hb zs hzs
    rw [← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose] at h
    exact h.trans hrate

/-- For an approximate block encoding with contractive normalized target and an odd unit-phase
list, the actual compressed word has error at most `4 * zs.length * √(ε / α)` and uses
exactly `zs.length` oracle queries [GilyenSuLowWiebe2019]. -/
theorem complex_boundary_actual_encoded_word :
    ∀ (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (U : Matrix H H ℂ)
      (L : Matrix H O ℂ) (R : Matrix H I ℂ) (α ε : ℝ) (base : ℂ) (zs : List ℂ),
      BlockEncoding A U L R α ε → ‖(α⁻¹ : ℝ) • A‖ ≤ 1 →
      IsPhase base → (∀ z ∈ zs, IsPhase z) → zs.length % 2 = 1 →
      ‖compress L (phasedAlternating U (rangeProjector R) (rangeProjector L) base zs) R -
        oddSingularTransform ((α⁻¹ : ℝ) • A) (interiorResponse base zs)‖ ≤
        4*zs.length*Real.sqrt (ε/α) ∧
      adjointQueryCount (compileQSVT (rangeProjector R) (rangeProjector L) base zs) = zs.length := by
  intro H I O _ _ _ _ _ _ A U L R α ε base zs h hA hb hzs hodd
  obtain ⟨hcorner, hquery⟩ := interior_complex_actual_corner_and_query_count H I O
    (compress L U R) U L R base zs (decodedBlock_projectedEncoding h) hodd
  refine ⟨?_, hquery⟩
  rw [hcorner, norm_sub_rev]
  exact ((complex_boundary_singular_response_stability I O ((α⁻¹ : ℝ) • A)
    (compress L U R) base zs hb hzs hA (decodedBlock_norm_le_one h)).1 hodd).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (encodedBlock_normalized_error h)) (by positivity))

end Qatlib.Concepts.QsvtCore.QsVtStability
