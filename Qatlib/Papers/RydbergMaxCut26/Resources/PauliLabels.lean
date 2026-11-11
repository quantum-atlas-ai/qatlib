/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.Resources.MomentCounts
import Qatlib.Papers.RydbergMaxCut26.MomentSdp.PauliRotation

/-!
# Pauli labels and the full moment matrix

`labelMatrix` realizes each level-two label as a tensor Pauli operator, and `wordSupport`
records its zero-, one-, or two-site support. Their real Gram moments form `fullMoment`;
`xyEmbedding` and `completionEmbedding` include the smaller X/Y index and variable sets in the
full construction.

These results support the development of [CrostaSaubanereHuber2026].

## Main statements

* `fullMoment_positive` and `fullMoment_diagonal`: establish positivity and trace-one diagonal
  normalization.
* `actual_variable_comparison`: compares completion and full variable counts via an embedding.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Matrix Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ChannelTheory.Stinespring
open scoped Classical ComplexOrder
namespace Qatlib.Papers.RydbergMaxCut26.Resources.Labels
open Qatlib.Papers.RydbergMaxCut26.Resources.Counts
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TensorProduct
open Qatlib.Papers.RydbergMaxCut26.MomentSdp.Rotation

/-- The tensor register operator whose local identity or Pauli factors are specified by
`labelWord l`. -/
noncomputable def labelMatrix {n : ℕ} (l : LevelTwoLabel n) : Matrix (Reg n) (Reg n) ℂ :=
  qubitTensor (fun i => match labelWord l i with | none => 1 | some a => pauliMatrix a)

/-- The matrix associated with the identity label is the register identity. -/
theorem identity_matrix (n : ℕ) : labelMatrix (n:=n) (Sum.inl PUnit.unit)=1 := qubitTensor_one n

/-- The matrix associated with a single-site label `(i, a)` is `sitePauli n i a`. -/
theorem single_matrix {n : ℕ} (i : Fin n) (a : Fin 3) :
    labelMatrix (Sum.inr (Sum.inl (i,a)))=sitePauli n i a := by
  unfold labelMatrix sitePauli
  congr 1
  funext h
  by_cases hi : h=i <;> simp only [labelWord,hi,ite_true,ite_false]

/-- The finite set of sites at which `labelWord l` specifies a Pauli factor. -/
noncomputable def wordSupport {n : ℕ} (l : LevelTwoLabel n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (labelWord l i).isSome)

/-- The support of the identity label has cardinality zero. -/
theorem identity_support (n : ℕ) : (wordSupport (n:=n) (Sum.inl PUnit.unit)).card=0 := by
  simp [wordSupport,labelWord]

/-- The support of a single-site Pauli label has cardinality one. -/
theorem single_support {n : ℕ} (i : Fin n) (a : Fin 3) :
    (wordSupport (Sum.inr (Sum.inl (i,a)))).card=1 := by
  have he : wordSupport (Sum.inr (Sum.inl (i,a)))={i} := by
    ext h
    simp [wordSupport,labelWord]
  rw [he,Finset.card_singleton]

/-- The support of a distinct-site double Pauli label has cardinality two. -/
theorem double_support {n : ℕ} (s : SitePair n) (f : s.1.toFinset → Fin 3) :
    (wordSupport (Sum.inr (Sum.inr ⟨s,f⟩))).card=2 := by
  have he : wordSupport (Sum.inr (Sum.inr ⟨s,f⟩))=s.1.toFinset := by
    ext h
    simp [wordSupport,labelWord]
  rw [he,Sym2.card_toFinset_of_not_isDiag _ s.2]

/-- Every labelled tensor Pauli matrix satisfies `(labelMatrix l)ᴴ * labelMatrix l = 1`. -/
theorem label_unitary {n : ℕ} (l : LevelTwoLabel n) : (labelMatrix l)ᴴ*labelMatrix l=1 := by
  rw [labelMatrix,qubitTensor_conjTranspose,qubitTensor_mul]
  have he : (fun i => (match labelWord l i with | none => (1 : Operator 2) | some a => pauliMatrix a)ᴴ*
      (match labelWord l i with | none => (1 : Operator 2) | some a => pauliMatrix a))=
      (fun _ : Fin n => (1 : Operator 2)) := by
    funext i
    cases labelWord l i <;> simp only
        [Matrix.conjTranspose_one,Matrix.one_mul,axis_adjoint,axis_square]
  rw [he,qubitTensor_one]

/-- The real moment matrix of the full level-two tensor Pauli family against `ρ`. -/
noncomputable def fullMoment {n : ℕ} (ρ : Matrix (Reg n) (Reg n) ℂ) :
    Matrix (LevelTwoLabel n) (LevelTwoLabel n) ℝ :=
  Qatlib.Papers.RydbergMaxCut26.MomentSdp.DensityMoment.realMoment labelMatrix ρ

/-- For positive semidefinite `ρ`, the full level-two real moment matrix is positive
semidefinite, as required for the relaxation compared in [CrostaSaubanereHuber2026]. -/
theorem fullMoment_positive {n : ℕ} (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) :
    (fullMoment ρ).PosSemidef :=
  Qatlib.Papers.RydbergMaxCut26.MomentSdp.DensityMoment.realMoment_posSemidef labelMatrix ρ hρ

/-- If `ρ` has trace one, every diagonal entry of `fullMoment ρ` is one. -/
theorem fullMoment_diagonal {n : ℕ} (ρ : Matrix (Reg n) (Reg n) ℂ) (htr : ρ.trace=1) (l : LevelTwoLabel n) :
    fullMoment ρ l l=1 :=
  Qatlib.Papers.RydbergMaxCut26.MomentSdp.DensityMoment.realMoment_diag labelMatrix label_unitary ρ htr l

/-- The embedding of vertex-X/Y moment indices into the single-site labels of `LevelTwoLabel n`. -/
def xyEmbedding (n : ℕ) : Qatlib.Papers.RydbergMaxCut26.MomentSdp.Gram.MomentIndex n ↪ LevelTwoLabel n where
  toFun p := Sum.inr (Sum.inl (p.1,⟨p.2.val,by omega⟩))
  inj' := by
    intro p q h
    simp only [Sum.inr.injEq,Sum.inl.injEq,Prod.mk.injEq] at h
    exact Prod.ext h.1 (Fin.ext (congrArg (fun a : Fin 3 => a.val) h.2))

/-- The embedding of symmetric X/Y completion variables into the full symmetric moment variables
induced by `xyEmbedding`. -/
def completionEmbedding (n : ℕ) : CompletionVariable n ↪ FullVariable n := (xyEmbedding n).sym2Map

/-- The number of X/Y completion variables is at most the number of full level-two symmetric
moment variables, formalizing the resource comparison of [CrostaSaubanereHuber2026]. -/
theorem actual_variable_comparison (n : ℕ) :
    Fintype.card (CompletionVariable n) ≤ Fintype.card (FullVariable n) :=
  Fintype.card_le_of_injective _ (completionEmbedding n).injective
end Qatlib.Papers.RydbergMaxCut26.Resources.Labels
