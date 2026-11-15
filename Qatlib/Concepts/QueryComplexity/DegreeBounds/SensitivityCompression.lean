/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QueryComplexity.DegreeBounds.BooleanFaces

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryComplexity.TriangleDegreeBounds Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
namespace Qatlib.Concepts.QueryComplexity.DegreeBounds
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-- Compressing a complex matrix along an injective index map does not increase its norm. -/
theorem sensitivity_injective_matrix_compression {X Y : Type} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y] (e : Y ↪ X) (A : Matrix X X ℂ) :
    ‖A.submatrix e e‖ ≤ ‖A‖ := by
  classical
  let V : Matrix X Y ℂ := fun x y => if x=e y then 1 else 0
  have hV : Vᴴ*V=1 := by
    ext i j
    simp [V,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply,e.injective.eq_iff,eq_comm]
  have hcomp : A.submatrix e e=Vᴴ*A*V := by
    ext i j
    simp [V,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.submatrix]
  have hn : ‖V‖=1 := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self V
    rw [hV,norm_one] at h
    nlinarith [norm_nonneg V]
  rw [hcomp]
  calc
    _ ≤ ‖Vᴴ*A‖*‖V‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖Vᴴ‖*‖A‖)*‖V‖ := mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul Vᴴ A) (norm_nonneg _)
    _ = ‖A‖ := by rw [Matrix.l2_opNorm_conjTranspose,hn,one_mul,mul_one]

/-- The embedding of a Boolean face into the full cube is injective. -/
theorem faceEmbedding_injective {I : Type} [DecidableEq I] (s : Finset I) :
    Function.Injective (faceEmbedding s) := by
  intro x y he
  ext i
  have h := congrFun he i
  simpa [faceEmbedding,i.property] using h

/-- Embedding two face vertices preserves the number of coordinates in which they differ. -/
private theorem face_difference_card {I : Type} [Fintype I] [DecidableEq I]
    (s : Finset I) (x y : s → Bool) :
    (Finset.univ.filter (fun i : I => faceEmbedding s x i ≠ faceEmbedding s y i)).card=
      (Finset.univ.filter (fun i : s => x i ≠ y i)).card := by
  classical
  have hs : Finset.univ.filter (fun i : I => faceEmbedding s x i ≠ faceEmbedding s y i)=
      (Finset.univ.filter (fun i : s => x i ≠ y i)).image Subtype.val := by
    ext i
    by_cases hi : i ∈ s
    · simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
      constructor
      · intro hd
        exact ⟨⟨i,hi⟩, by simpa [faceEmbedding,hi] using hd,rfl⟩
      · rintro ⟨j,hj,rfl⟩
        simpa [faceEmbedding,j.property] using hj
    · simp [faceEmbedding,hi]
  rw [hs,Finset.card_image_of_injective _ Subtype.val_injective]

/-- Restricting a Boolean function to a face does not increase its spectral sensitivity. -/
theorem sensitivity_face_norm_le {I : Type} [Fintype I] [DecidableEq I]
    (f : (I → Bool) → Bool) (s : Finset I) :
    spectralSensitivity (fun x : s → Bool => f (faceEmbedding s x)) ≤ spectralSensitivity f := by
  classical
  let e : (s → Bool) ↪ (I → Bool) := ⟨faceEmbedding s,faceEmbedding_injective s⟩
  have hm : sensAdjacency (fun x : s → Bool => f (faceEmbedding s x))=
      (sensAdjacency f).submatrix e e := by
    ext x y
    change sensAdjacency (fun x : s → Bool => f (faceEmbedding s x)) x y=
      sensAdjacency f (faceEmbedding s x) (faceEmbedding s y)
    simp only [sensAdjacency,face_difference_card]
  change ‖sensAdjacency _‖ ≤ ‖sensAdjacency f‖
  rw [hm]
  exact sensitivity_injective_matrix_compression e _

noncomputable def cubeMap {I J : Type} (e : J ≃ I) (x : J → Bool) : I → Bool := x ∘ e.symm

/-- Reindexing cube coordinates along an equivalence preserves the parity sign. -/
theorem cubeMap_sign {I J : Type} [Fintype I] [Fintype J] (e : J ≃ I) (x : J → Bool) :
    cubeSign (cubeMap e x)=cubeSign x := by
  unfold cubeSign
  exact (e.symm.prod_comp (fun j => if x j then (-1 : ℝ) else 1))

/-- Reindexing a Boolean function along a coordinate equivalence does not increase its spectral
sensitivity. -/
theorem sensitivity_cubeMap_norm_le {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : J ≃ I) (f : (I → Bool) → Bool) :
    spectralSensitivity (fun x : J → Bool => f (cubeMap e x)) ≤ spectralSensitivity f := by
  classical
  have hi : Function.Injective (cubeMap e) := by
    intro x y he
    ext j
    have h := congrFun he (e j)
    simpa [cubeMap] using h
  let E : (J → Bool) ↪ (I → Bool) := ⟨cubeMap e,hi⟩
  have hcard (x y : J → Bool) :
      (Finset.univ.filter (fun i : I => cubeMap e x i ≠ cubeMap e y i)).card=
        (Finset.univ.filter (fun j : J => x j ≠ y j)).card := by
    have he : Finset.univ.filter (fun i : I => cubeMap e x i ≠ cubeMap e y i)=
        (Finset.univ.filter (fun j : J => x j ≠ y j)).image e := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
      constructor
      · intro h
        exact ⟨e.symm i,h,e.apply_symm_apply i⟩
      · rintro ⟨j,hj,rfl⟩
        simpa [cubeMap] using hj
    rw [he,Finset.card_image_of_injective _ e.injective]
  have hm : sensAdjacency (fun x : J → Bool => f (cubeMap e x))=
      (sensAdjacency f).submatrix E E := by
    ext x y
    change sensAdjacency (fun x : J → Bool => f (cubeMap e x)) x y=
      sensAdjacency f (cubeMap e x) (cubeMap e y)
    simp only [sensAdjacency,hcard]
  change ‖sensAdjacency _‖ ≤ ‖sensAdjacency f‖
  rw [hm]
  exact sensitivity_injective_matrix_compression E _

end Qatlib.Concepts.QueryComplexity.DegreeBounds
