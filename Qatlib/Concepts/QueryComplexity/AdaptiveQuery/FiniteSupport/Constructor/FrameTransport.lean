/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.ConstructorPromise
import Qatlib.Concepts.ChoiKraus.ChoiKrausChar.ChannelStructure
import Qatlib.Concepts.ChannelTheory.Stinespring.ChannelStructureStinespring

open Qatlib.Concepts.BlockEncoding.LCU

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Foundations.PureStateMath

/-!
# Frame Transport

Extension only uses the classically known frame and slot map. Neither unknown oracle matrices nor the target matrix enter the selected unitary.
-/
open Qatlib Matrix
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol
open scoped BigOperators Classical ComplexOrder
set_option autoImplicit false
set_option maxRecDepth 2048
noncomputable section

namespace Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor
/-- The finite protocol identity or bound `basisFrame_isometry` holds under exactly the displayed hypotheses. -/
theorem basisFrame_isometry {D : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (φ : I → Fin D) (hφ : Function.Injective φ) : IsIsometry (basisFrame φ) := by
  ext i j
  simp [basisFrame,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply,hφ.eq_iff,eq_comm]

/-- Extension only uses the classically known frame and slot map. Neither
unknown oracle matrices nor the target matrix enter the selected unitary. -/
theorem exists_frame_alignment {D : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (φ : I → Fin D) (hφ : Function.Injective φ) (F : Matrix (Fin D) I ℂ) (hF : IsIsometry F) :
    ∃ U : Operator D,U∈Matrix.unitaryGroup (Fin D) ℂ ∧ U*basisFrame φ=F := by
  let e := Fintype.equivFin I
  let W : Matrix (Fin D) (Fin (Fintype.card I)) ℂ := F.submatrix id e.symm
  let emb : Fin (Fintype.card I) → Fin D := fun j => φ (e.symm j)
  have hemb : Function.Injective emb := hφ.comp e.symm.injective
  have hW : W.conjTranspose*W=1 := by
    ext i j
    have hh := congrArg (fun M : Matrix I I ℂ => M (e.symm i) (e.symm j)) hF
    simpa [W,IsIsometry,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply,e.symm.injective.eq_iff] using hh
  obtain ⟨U,hU1,hU2,hcols⟩ := Qatlib.Concepts.ChannelTheory.Stinespring.exists_unitary_extend_cols W emb hemb hW
  refine ⟨U,?_,?_⟩
  · rw [Matrix.mem_unitaryGroup_iff,Matrix.star_eq_conjTranspose]
    exact hU2
  · ext x j
    have he := hcols x (e j)
    simpa [Matrix.mul_apply,basisFrame,emb,W] using he

/-- Invalid failed-output frames use the identity fallback, keeping every
record. This is a query-independent mathematical known-unitary choice, not
an efficient physical frame-preparation algorithm. -/
def frameAlignment {D : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (φ : I → Fin D) (hφ : Function.Injective φ) (F : Matrix (Fin D) I ℂ) : Operator D :=
  if hF : IsIsometry F then (exists_frame_alignment φ hφ F hF).choose else 1

/-- The finite protocol identity or bound `frameAlignment_unitary` holds under exactly the displayed hypotheses. -/
theorem frameAlignment_unitary {D : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (φ : I → Fin D) (hφ : Function.Injective φ) (F : Matrix (Fin D) I ℂ) :
    frameAlignment φ hφ F∈Matrix.unitaryGroup (Fin D) ℂ := by
  unfold frameAlignment
  split_ifs with hF
  · exact (exists_frame_alignment φ hφ F hF).choose_spec.1
  · exact (Matrix.unitaryGroup (Fin D) ℂ).one_mem

/-- The finite protocol identity or bound `frameAlignment_frame` holds under exactly the displayed hypotheses. -/
theorem frameAlignment_frame {D : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (φ : I → Fin D) (hφ : Function.Injective φ) (F : Matrix (Fin D) I ℂ) (hF : IsIsometry F) :
    frameAlignment φ hφ F*basisFrame φ=F := by
  unfold frameAlignment
  rw [dite_eq_left hF]
  exact (exists_frame_alignment φ hφ F hF).choose_spec.2

/-- The finite protocol identity or bound `wordMatrix_append` holds under exactly the displayed hypotheses. -/
theorem wordMatrix_append {D : ℕ} (O : Bool → Operator D) (gs hs : List (OutputGate D)) :
    wordMatrix O (gs++hs)=wordMatrix O hs*wordMatrix O gs := by
  induction gs with
  | nil => simp [wordMatrix]
  | cons g gs ih => simp [wordMatrix,ih,Matrix.mul_assoc]

/-- The finite protocol identity or bound `wordQueries_append` holds under exactly the displayed hypotheses. -/
theorem wordQueries_append {D : ℕ} (gs hs : List (OutputGate D)) :
    wordQueries (gs++hs)=wordQueries gs+wordQueries hs := by
  induction gs with
  | nil => simp [wordQueries]
  | cons g gs ih => cases g <;> simp [wordQueries,ih,Nat.add_assoc,Nat.add_comm 1]

/-- Construction for coordinate Word in the frame transport model. -/
def coordinateWord {D : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (φ : I → Fin D) (hφ : Function.Injective φ) (L R : Matrix (Fin D) I ℂ)
    (gs : List (OutputGate D)) : List (OutputGate D) :=
  .known (frameAlignment φ hφ R) (frameAlignment_unitary φ hφ R)::
    (gs++[.known (frameAlignment φ hφ L).conjTranspose (adjoint_unitary (frameAlignment_unitary φ hφ L))])

/-- The finite protocol identity or bound `coordinateWord_matrix` holds under exactly the displayed hypotheses. -/
theorem coordinateWord_matrix {D : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (φ : I → Fin D) (hφ : Function.Injective φ) (L R : Matrix (Fin D) I ℂ)
    (O : Bool → Operator D) (gs : List (OutputGate D)) :
    wordMatrix O (coordinateWord φ hφ L R gs)=
      (frameAlignment φ hφ L).conjTranspose*wordMatrix O gs*frameAlignment φ hφ R := by
  simp [coordinateWord,wordMatrix,wordMatrix_append,gateMatrix,Matrix.mul_assoc]

/-- The finite protocol identity or bound `coordinateWord_queries` holds under exactly the displayed hypotheses. -/
theorem coordinateWord_queries {D : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (φ : I → Fin D) (hφ : Function.Injective φ) (L R : Matrix (Fin D) I ℂ)
    (gs : List (OutputGate D)) : wordQueries (coordinateWord φ hφ L R gs)=wordQueries gs := by
  simp [coordinateWord,wordQueries,wordQueries_append]

/-- The finite protocol identity or bound `coordinateWord_encoding` holds under exactly the displayed hypotheses. -/
theorem coordinateWord_encoding {D : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (φ : I → Fin D) (hφ : Function.Injective φ) (L R : Matrix (Fin D) I ℂ)
    (O : Bool → Operator D) (gs : List (OutputGate D)) (T : Matrix I I ℂ) (α ε : ℝ)
    (hc : BlockEncoding T (wordMatrix O gs) L R α ε) :
    BlockEncoding T (wordMatrix O (coordinateWord φ hφ L R gs)) (basisFrame φ) (basisFrame φ) α ε := by
  have hcomp : compress (basisFrame φ) (wordMatrix O (coordinateWord φ hφ L R gs)) (basisFrame φ)=
      compress L (wordMatrix O gs) R := by
    rw [coordinateWord_matrix]
    unfold compress
    calc
      _ = (frameAlignment φ hφ L*basisFrame φ).conjTranspose*wordMatrix O gs*
          (frameAlignment φ hφ R*basisFrame φ) := by simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
      _ = _ := by rw [frameAlignment_frame φ hφ L hc.left_isometry,frameAlignment_frame φ hφ R hc.right_isometry]
  refine ⟨?_,basisFrame_isometry φ hφ,basisFrame_isometry φ hφ,hc.normalization_pos,hc.error_nonneg,?_⟩
  · rw [coordinateWord_matrix]
    exact (Matrix.unitaryGroup (Fin D) ℂ).mul_mem
      ((Matrix.unitaryGroup (Fin D) ℂ).mul_mem (adjoint_unitary (frameAlignment_unitary φ hφ L)) hc.unitary)
      (frameAlignment_unitary φ hφ R)
  · rw [hcomp]
    exact hc.error_le

/-- Construction for framed Promise in the frame transport model. -/
def framedPromise {D R : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (O : Bool → Operator D) (hO : ∀ mode,O mode∈Matrix.unitaryGroup (Fin D) ℂ) (S : ℝ → Fin R)
    (P : Program D R) (words : Path P → List (OutputGate D))
    (L Rf : Path P → Matrix (Fin D) I ℂ) (T : Matrix I I ℂ) (τ : ℝ) (r0 : Fin D) : Prop :=
  ∃ G : Finset (Path P),
    2/3 ≤ (∑ p∈G,(preparedLaw (fun mode => unitaryChannel (O mode) (hO mode)) S r0 P).prob p) ∧
    ∀ p∈G,BlockEncoding T (wordMatrix O (words p)) (L p) (Rf p) 1 (τ/100)

/-- The finite protocol identity or bound `framedPromise_coordinate` holds under exactly the displayed hypotheses. -/
theorem framedPromise_coordinate {D R : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (φ : I → Fin D) (hφ : Function.Injective φ)
    (O : Bool → Operator D) (hO : ∀ mode,O mode∈Matrix.unitaryGroup (Fin D) ℂ) (S : ℝ → Fin R)
    (P : Program D R) (words : Path P → List (OutputGate D))
    (L Rf : Path P → Matrix (Fin D) I ℂ) (T : Matrix I I ℂ) (τ : ℝ) (r0 : Fin D)
    (hc : framedPromise O hO S P words L Rf T τ r0) :
    constructorPromise O hO S P (fun p => coordinateWord φ hφ (L p) (Rf p) (words p))
      (fun _ => φ) T τ r0 := by
  rcases hc with ⟨G,hG,hgood⟩
  refine ⟨G,hG,?_⟩
  intro p hp
  exact coordinateWord_encoding φ hφ (L p) (Rf p) O (words p) T 1 (τ/100) (hgood p hp)


/-- The finite protocol identity or bound `coordinateWord_adjoint_matrix` holds under exactly the displayed hypotheses. -/
theorem coordinateWord_adjoint_matrix {D : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (φ : I → Fin D) (hφ : Function.Injective φ) (L R : Matrix (Fin D) I ℂ)
    (O : Bool → Operator D) (gs hs : List (OutputGate D))
    (hInv : wordMatrix O hs=(wordMatrix O gs).conjTranspose) :
    wordMatrix O (coordinateWord φ hφ R L hs)=
      (wordMatrix O (coordinateWord φ hφ L R gs)).conjTranspose := by
  rw [coordinateWord_matrix,coordinateWord_matrix,hInv]
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc]


end Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor
