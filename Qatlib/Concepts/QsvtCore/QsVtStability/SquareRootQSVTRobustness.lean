/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.QsVtMain.LengthQSVT
import Qatlib.Concepts.CoherentSim.CoherentOAA.BlockRobustness
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.Matrix.Order

/-!
# Square-root robustness of real polynomial QSVT

This module proves the one-half Hölder estimate for positive matrix square roots and uses
defect-square-root unitaries to encode rectangular contractions. The matrix square-root
estimates are backgrounded by [Bhatia1997]. These estimates lead to the square-root
singular-transform robustness bound in [GilyenSuLowWiebe2019].

For a real polynomial bounded by one on `[-1, 1]`, with degree bound `d` and matching parity,
the corresponding singular transforms differ by at most `4 * d * √‖A - B‖`.

## Main statements

* `positive_matrix_square_root_holder`: Bound square-root differences of positive semidefinite
  matrices.
* `real_singular_polynomial_root_robustness`: Bound real polynomial singular transforms for both
  parities.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
* [Bhatia, 1997][Bhatia1997]
-/

open Qatlib.Concepts.BlockEncoding.Postselection

open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QsvtCore.LinearSystems
open Qatlib.Concepts.WalkSearch.Spectral

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
namespace Qatlib.Concepts.QsvtCore.QsVtStability
open Matrix Polynomial Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

noncomputable local instance rootMatrixCStar {I : Type} [Fintype I] [DecidableEq I] :
    CStarAlgebra (Matrix I I ℂ) where

/-- A nonnegative real scalar maps to a nonnegative scalar matrix. -/
private theorem root_scalar_nonneg {I : Type} [Fintype I] [DecidableEq I]
    {r : ℝ} (hr : 0 ≤ r) : 0 ≤ algebraMap ℝ (Matrix I I ℂ) r := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact ((Matrix.PosSemidef.one : (1 : Matrix I I ℂ).PosSemidef).smul hr).nonneg

/-- A self-adjoint matrix between the scalar bounds `-r` and `r` has norm at most `r`, for
nonnegative `r`. -/
private theorem root_norm_of_order_bounds {I : Type} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) (hX : IsSelfAdjoint X) (r : ℝ) (hr : 0 ≤ r)
    (hlo : algebraMap ℝ (Matrix I I ℂ) (-r) ≤ X)
    (hhi : X ≤ algebraMap ℝ (Matrix I I ℂ) r) : ‖X‖ ≤ r := by
  by_cases hI : Nonempty I
  · letI := hI
    rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum (a := X) hX with h | h
    · exact (le_algebraMap_iff_spectrum_le hX).mp hhi _ h
    · have hh := (algebraMap_le_iff_le_spectrum hX).mp hlo _ h
      linarith
  · letI : IsEmpty I := not_nonempty_iff.mp hI
    have hzero : X = 0 := by ext i; exact isEmptyElim i
    simpa [hzero] using hr

/-- For a nonnegative matrix `B` and nonnegative `δ`, `√(B + δ I) ≤ √B + √δ I`. -/
private theorem root_sqrt_shift_le {I : Type} [Fintype I] [DecidableEq I]
    (B : Matrix I I ℂ) (hB : 0 ≤ B) (δ : ℝ) (hδ : 0 ≤ δ) :
    CFC.sqrt (B + algebraMap ℝ (Matrix I I ℂ) δ) ≤
      CFC.sqrt B + algebraMap ℝ (Matrix I I ℂ) (Real.sqrt δ) := by
  let S := CFC.sqrt B
  let t := algebraMap ℝ (Matrix I I ℂ) (Real.sqrt δ)
  have hS : 0 ≤ S := CFC.sqrt_nonneg B
  have ht : 0 ≤ t := root_scalar_nonneg (Real.sqrt_nonneg δ)
  have hst : S * t = t * S := (Algebra.commutes (Real.sqrt δ) S).symm
  have hsq : t * t = algebraMap ℝ (Matrix I I ℂ) δ := by
    rw [← map_mul, Real.mul_self_sqrt hδ]
  have hcross : 0 ≤ t * S := by
    rw [show t * S = (Real.sqrt δ) • S by simp [t,Algebra.algebraMap_eq_smul_one]]
    exact (hS.posSemidef.smul (Real.sqrt_nonneg δ)).nonneg
  have hle : B + algebraMap ℝ (Matrix I I ℂ) δ ≤ (S + t) * (S + t) := by
    rw [add_mul,mul_add,mul_add,hst,hsq,show S*S=B from CFC.sqrt_mul_sqrt_self B hB]
    simpa only [add_assoc,add_comm,add_left_comm] using
      le_add_of_nonneg_right (a := B + algebraMap ℝ (Matrix I I ℂ) δ)
        (add_nonneg hcross hcross)
  have h := CFC.sqrt_le_sqrt (B + algebraMap ℝ (Matrix I I ℂ) δ) ((S+t)*(S+t)) hle
  have he : CFC.sqrt ((S+t)*(S+t)) = S+t := CFC.sqrt_mul_self (S+t) (add_nonneg hS ht)
  exact h.trans_eq he

/-- Positive semidefinite matrix square roots satisfy `‖√A - √B‖ ≤ √‖A - B‖`. See [Bhatia1997]. -/
theorem positive_matrix_square_root_holder :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (A B : Matrix I I ℂ),
      A.PosSemidef → B.PosSemidef →
      ‖CFC.sqrt A - CFC.sqrt B‖ ≤ Real.sqrt ‖A - B‖ := by
  intro I _ _ A B hA hB
  have upper (X Y : Matrix I I ℂ) (hX : X.PosSemidef) (hY : Y.PosSemidef) :
      CFC.sqrt X - CFC.sqrt Y ≤
        algebraMap ℝ (Matrix I I ℂ) (Real.sqrt ‖X-Y‖) := by
    have hXY := (hX.isHermitian.sub hY.isHermitian).isSelfAdjoint.le_algebraMap_norm_self
    have hXY' : X ≤ Y + algebraMap ℝ (Matrix I I ℂ) ‖X-Y‖ := by
      simpa only [add_comm] using (sub_le_iff_le_add).mp hXY
    have h := (CFC.sqrt_le_sqrt _ _ hXY').trans
      (root_sqrt_shift_le Y hY.nonneg ‖X-Y‖ (norm_nonneg _))
    exact (sub_le_iff_le_add).mpr (by simpa only [add_comm] using h)
  have hhi := upper A B hA hB
  have hlo := upper B A hB hA
  rw [norm_sub_rev] at hlo
  apply root_norm_of_order_bounds _
    ((CFC.sqrt_nonneg A).isSelfAdjoint.sub (CFC.sqrt_nonneg B).isSelfAdjoint)
    (Real.sqrt ‖A-B‖) (Real.sqrt_nonneg _) _ hhi
  rw [map_neg,neg_le]
  simpa only [neg_sub] using hlo

/-- The defect square root `√(1 - X * X)` used in the robust unitary construction. -/
private noncomputable def rootDefect {I : Type} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) : Matrix I I ℂ := CFC.sqrt (1-X*X)

/-- The squared defect of a Hermitian contraction is nonnegative. -/
private theorem rootDefect_positive {I : Type} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) (hX : X.IsHermitian) (hn : ‖X‖ ≤ 1) : 0 ≤ 1-X*X := by
  have h := CStarAlgebra.star_mul_le_algebraMap_norm_sq (a := X)
  rw [Matrix.star_eq_conjTranspose,hX] at h
  have hscalar : algebraMap ℝ (Matrix I I ℂ) (‖X‖^2) ≤ 1 := by
    rw [← map_one (algebraMap ℝ (Matrix I I ℂ)),← sub_nonneg,← map_sub]
    apply root_scalar_nonneg
    nlinarith [norm_nonneg X]
  exact sub_nonneg.mpr (h.trans hscalar)

/-- A matrix commutes with its defect square root. -/
private theorem rootDefect_commute {I : Type} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) : X * rootDefect X = rootDefect X * X := by
  have hc : Commute (1-X*X) X := by change (1-X*X)*X=X*(1-X*X); noncomm_ring
  exact (hc.cfcₙ_nnreal NNReal.sqrt).eq.symm

/-- The block unitary candidate with diagonal blocks `X` and `-X` and defect square roots off
the diagonal. -/
private noncomputable def rootUnitary {I : Type} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) : Matrix (I⊕I) (I⊕I) ℂ :=
  Matrix.fromBlocks X (rootDefect X) (rootDefect X) (-X)

/-- The defect block construction is unitary for a Hermitian contraction. -/
private theorem rootUnitary_unitary {I : Type} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) (hX : X.IsHermitian) (hn : ‖X‖ ≤ 1) :
    rootUnitary X ∈ Matrix.unitaryGroup (I⊕I) ℂ := by
  have hS : (rootDefect X).IsHermitian := (CFC.sqrt_nonneg (1-X*X)).isSelfAdjoint
  have hx : Xᴴ=X := hX
  have hs : (rootDefect X)ᴴ=rootDefect X := hS
  have hsq : rootDefect X * rootDefect X = 1-X*X :=
    CFC.sqrt_mul_sqrt_self (1-X*X) (rootDefect_positive X hX hn)
  have hc := rootDefect_commute X
  rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose]
  simp only [rootUnitary,Matrix.fromBlocks_conjTranspose,Matrix.conjTranspose_neg,hx,hs,
    Matrix.fromBlocks_multiply,Matrix.mul_neg,Matrix.neg_mul,neg_neg,
    hsq,hc,add_sub_cancel,add_neg_cancel,sub_add_cancel]
  exact Matrix.fromBlocks_one

/-- The signed block diagonal matrix of a Hermitian `X` has norm at most `‖X‖`. -/
private theorem root_signed_diagonal_norm_le {I : Type} [Fintype I] [DecidableEq I]
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

/-- The squared defects of two contractions differ in norm by at most `2 * ‖X - Y‖`. -/
private theorem root_square_distance {I : Type} [Fintype I] [DecidableEq I]
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

/-- The defect block unitaries of two Hermitian contractions differ by at most `4 * √‖X - Y‖`. -/
private theorem rootUnitary_distance {I : Type} [Fintype I] [DecidableEq I]
    (X Y : Matrix I I ℂ) (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (hnX : ‖X‖ ≤ 1) (hnY : ‖Y‖ ≤ 1) :
    ‖rootUnitary X-rootUnitary Y‖ ≤ 4*Real.sqrt ‖X-Y‖ := by
  have hS : (rootDefect X-rootDefect Y).IsHermitian :=
    ((CFC.sqrt_nonneg (1-X*X)).isSelfAdjoint.sub
      (CFC.sqrt_nonneg (1-Y*Y)).isSelfAdjoint).isHermitian
  have he : rootUnitary X-rootUnitary Y =
      Matrix.fromBlocks (X-Y) 0 0 (-(X-Y)) + hermitianDilation (rootDefect X-rootDefect Y) := by
    have hs : (rootDefect X-rootDefect Y)ᴴ=rootDefect X-rootDefect Y := hS
    unfold rootUnitary hermitianDilation
    rw [hs]
    ext i j
    cases i <;> cases j <;> simp
    ring
  have hroot : ‖rootDefect X-rootDefect Y‖ ≤ Real.sqrt (2*‖X-Y‖) :=
    (positive_matrix_square_root_holder I (1-X*X) (1-Y*Y)
      (rootDefect_positive X hX hnX).posSemidef
      (rootDefect_positive Y hY hnY).posSemidef).trans
      (Real.sqrt_le_sqrt (root_square_distance X Y hnX hnY))
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
        ‖hermitianDilation (rootDefect X-rootDefect Y)‖ := norm_add_le _ _
    _ ≤ ‖X-Y‖+Real.sqrt (2*‖X-Y‖) := by
      rw [hermitianDilation_norm]
      exact add_le_add (root_signed_diagonal_norm_le (X-Y) (hX.sub hY)) hroot
    _ ≤ _ := by linarith

/-- The Hermitian dilation of a rectangular matrix is Hermitian. -/
private theorem root_dilation_hermitian {I O : Type} [Fintype I] [Fintype O]
    (A : Matrix O I ℂ) : (hermitianDilation A).IsHermitian := by
  unfold Matrix.IsHermitian hermitianDilation
  simp [Matrix.fromBlocks_conjTranspose]

/-- The embedding into the first copy of the doubled Hermitian-dilation space. -/
private noncomputable def rootFirst {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] : Matrix ((O⊕I)⊕(O⊕I)) (O⊕I) ℂ :=
  (dilationLeft (I := O⊕I) (O := O⊕I))ᴴ
/-- The output frame for the defect-unitary encoding of a rectangular matrix. -/
private noncomputable def rootLeft {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] : Matrix ((O⊕I)⊕(O⊕I)) O ℂ :=
  rootFirst (I := I) (O := O) * (dilationLeft (I := I) (O := O))ᴴ
/-- The input frame for the defect-unitary encoding of a rectangular matrix. -/
private noncomputable def rootRight {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] : Matrix ((O⊕I)⊕(O⊕I)) I ℂ :=
  rootFirst (I := I) (O := O) * (dilationRight (I := I) (O := O))ᴴ

/-- A rectangular contraction has a projected encoding by the defect unitary of its Hermitian
dilation. -/
private theorem root_projectedEncoding {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] (A : Matrix O I ℂ) (hn : ‖A‖ ≤ 1) :
    ProjectedUnitaryEncoding A (rootUnitary (hermitianDilation A)) rootLeft rootRight := by
  have hE : IsIsometry (rootFirst (I := I) (O := O)) :=
    dilationLeft_adjoint_isIsometry
  refine ⟨rootUnitary_unitary _ (root_dilation_hermitian A)
    (by simpa only [hermitianDilation_norm] using hn),
    Qatlib.Concepts.BlockEncoding.EncodingCore.IsIsometry.mul hE dilationLeft_adjoint_isIsometry,
    Qatlib.Concepts.BlockEncoding.EncodingCore.IsIsometry.mul hE dilationRight_adjoint_isIsometry, ?_⟩
  have he : compress (rootFirst (I := I) (O := O)) (rootUnitary (hermitianDilation A)) rootFirst =
      hermitianDilation A := by
    rw [rootFirst,compress_dilation_selectors11]
    rfl
  calc
    compress rootLeft (rootUnitary (hermitianDilation A)) rootRight =
      compress dilationLeftᴴ (compress rootFirst (rootUnitary (hermitianDilation A)) rootFirst)
        dilationRightᴴ := by
      unfold rootLeft rootRight compress
      rw [Matrix.conjTranspose_mul (rootFirst (I := I) (O := O))
        (dilationLeft (I := I) (O := O))ᴴ]
      simp only [Matrix.mul_assoc]
    _ = A := by rw [he,compress_dilation_selectors12]; rfl

/-- For fixed orthogonal projectors, isometric frames, and unit phases, compressed real-part
QSVT circuits differ by at most `zs.length * ‖U - V‖`. -/
private theorem root_average_oracle_error {H I O : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    {U V P Q : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (hU : U ∈ unitaryGroup H ℂ) (hV : V ∈ unitaryGroup H ℂ)
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q)
    (hL : IsIsometry L) (hR : IsIsometry R)
    {base : ℂ} (hb : IsPhase base) (zs : List ℂ) (hzs : ∀ z∈zs,IsPhase z) :
    ‖compress (averageFrame L) (realPartQSVT U P Q base zs) (averageFrame R)-
      compress (averageFrame L) (realPartQSVT V P Q base zs) (averageFrame R)‖ ≤
      (zs.length:ℝ)*‖U-V‖ := by
  have h0 := compress_phasedAlternating_oracle_error hL hR hU hV hP hQ hb zs hzs
  have h1 := compress_phasedAlternating_oracle_error hL hR hU hV hP hQ
    (Qatlib.Concepts.QspSimulation.Achievability.IsPhase.conjugate hb) (zs.map star) (phases_conjugate zs hzs)
  rw [List.length_map] at h1
  let a := compress L (phasedAlternating U P Q base zs) R
  let b := compress L (phasedAlternating U P Q (star base) (zs.map star)) R
  let c := compress L (phasedAlternating V P Q base zs) R
  let e := compress L (phasedAlternating V P Q (star base) (zs.map star)) R
  rw [realPartQSVT,realPartQSVT,averageCircuit_compress,averageCircuit_compress,← smul_sub]
  change ‖(2:ℂ)⁻¹ • ((a+b)-(c+e))‖ ≤ _
  rw [show (a+b)-(c+e)=(a-c)+(b-e) by abel,norm_smul]
  have hhalf : ‖(2:ℂ)⁻¹‖ = (2:ℝ)⁻¹ := by norm_num
  rw [hhalf]
  calc
    _ ≤ (2:ℝ)⁻¹*(‖a-c‖+‖b-e‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ ≤ _ := by dsimp only [a,b,c,e]; linarith

/-- A bounded real polynomial of degree at most `d` and parity `d` transforms contractions with
error at most `4 * d * √‖A - B‖`, using the parity-appropriate singular transform
[GilyenSuLowWiebe2019]. -/
theorem real_singular_polynomial_root_robustness :
    ∀ (I O : Type) [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
      (A B : Matrix O I ℂ) (p : Polynomial ℝ) (d : ℕ),
      ‖A‖ ≤ 1 → ‖B‖ ≤ 1 → p.degree ≤ (d : WithBot ℕ) → HasRealParity d p →
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ 1) →
      (d % 2 = 1 →
        ‖oddSingularTransform A (fun x => ((p.eval x : ℝ) : ℂ)) -
          oddSingularTransform B (fun x => ((p.eval x : ℝ) : ℂ))‖ ≤ 4*d*Real.sqrt ‖A-B‖) ∧
      (d % 2 = 0 →
        ‖rightSingularTransform A (fun x => ((p.eval x : ℝ) : ℂ)) -
          rightSingularTransform B (fun x => ((p.eval x : ℝ) : ℂ))‖ ≤ 4*d*Real.sqrt ‖A-B‖) := by
  intro I O _ _ _ _ A B p d hA hB hp hpar hbounded
  obtain ⟨base,zs,hbase,hzs,hlen,_,hre⟩ := exists_phases_of_bounded hp hpar hbounded
  have hfun : (fun x : ℝ => (((responseP base zs).eval (x:ℂ)).re:ℂ)) =
      (fun x : ℝ => ((p.eval x:ℝ):ℂ)) := by
    funext x; exact congrArg Complex.ofReal (hre x)
  have hEA := root_projectedEncoding A hA
  have hEB := root_projectedEncoding B hB
  have hP := rangeProjector_isOrthogonalProjector hEA.right_isometry
  have hQ := rangeProjector_isOrthogonalProjector hEA.left_isometry
  have hdist : ‖rootUnitary (hermitianDilation A)-rootUnitary (hermitianDilation B)‖ ≤
      4*Real.sqrt ‖A-B‖ := by
    simpa only [hermitianDilation_sub_norm] using rootUnitary_distance
      (hermitianDilation A) (hermitianDilation B)
      (root_dilation_hermitian A) (root_dilation_hermitian B)
      (by simpa only [hermitianDilation_norm] using hA)
      (by simpa only [hermitianDilation_norm] using hB)
  constructor
  · intro hodd
    have h0 := realPartQSVT_odd_singularEncoding hEA hbase zs hzs (by simpa [hlen] using hodd)
    have h1 := realPartQSVT_odd_singularEncoding hEB hbase zs hzs (by simpa [hlen] using hodd)
    rw [hfun] at h0 h1
    rw [← h0.encoded,← h1.encoded]
    exact (root_average_oracle_error hEA.unitary hEB.unitary hP hQ
      hEA.left_isometry hEA.right_isometry hbase zs hzs).trans (by
        rw [hlen]
        nlinarith [mul_le_mul_of_nonneg_left hdist (Nat.cast_nonneg d : (0:ℝ)≤d)])
  · intro heven
    have h0 :=
        realPartQSVT_even_right_singularEncoding hEA hbase zs hzs (by simpa [hlen] using heven)
    have h1 :=
        realPartQSVT_even_right_singularEncoding hEB hbase zs hzs (by simpa [hlen] using heven)
    rw [hfun] at h0 h1
    rw [← h0.encoded,← h1.encoded]
    exact (root_average_oracle_error (adjoint_unitary hEA.unitary) (adjoint_unitary hEB.unitary)
      hQ hP hEA.right_isometry hEA.right_isometry hbase zs hzs).trans (by
        rw [hlen,← Matrix.conjTranspose_sub,Matrix.l2_opNorm_conjTranspose]
        nlinarith [mul_le_mul_of_nonneg_left hdist (Nat.cast_nonneg d : (0:ℝ)≤d)])

end Qatlib.Concepts.QsvtCore.QsVtStability
