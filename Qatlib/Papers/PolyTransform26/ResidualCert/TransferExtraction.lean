/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PolyTransform26.ResidualCert.TransferExtractionData
import Qatlib.Papers.PolyTransform26.ResidualCert.Basic
import Qatlib.Concepts.MpsAdaptation.MpsTransfer.GramContraction
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.MpsAdaptation.MpsTransfer
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Foundations.MatrixAlgebra.ResponseAlgebra

namespace Qatlib.Papers.PolyTransform26.ResidualCert
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
variable {X Y J : Type} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [Fintype J] [DecidableEq J]

omit [DecidableEq X] [DecidableEq Y] [Fintype J] [DecidableEq J] in

theorem compact_successor_blocks {r : ℕ} (F : J → Matrix Y X ℂ)
    (Q : Matrix X (Fin r) ℂ) (a0 : EuclideanSpace ℂ (Fin r))
    (Ares : J → Matrix (Fin r) (Fin r) ℂ) (d : ℂ) (pRow : J → Fin r → ℂ)
    (V : Matrix (X ⊕ Unit) (Y ⊕ Unit) ℂ)
    (he : V*compactSuccessorInput F Q=compactSuccessorOutput Q a0 Ares d pRow) :
    (∀ x, V (Sum.inl x) (Sum.inr ())=Q.mulVec a0 x) ∧
    V (Sum.inr ()) (Sum.inr ())=d ∧
    (∀ j, (V.submatrix Sum.inl Sum.inl)*(F j*Q)=Q*Ares j) ∧
    (∀ j t, ∑ y, V (Sum.inr ()) (Sum.inl y)*(F j*Q) y t=pRow j t) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro x
    have h := congrArg (fun M => M (Sum.inl x) (Sum.inl ())) he
    simpa [Matrix.mul_apply,compactSuccessorInput,compactSuccessorOutput,Fintype.sum_sum_type] using h
  · have h := congrArg (fun M => M (Sum.inr ()) (Sum.inl ())) he
    simpa [Matrix.mul_apply,compactSuccessorInput,compactSuccessorOutput,Fintype.sum_sum_type] using h
  · intro j
    ext x t
    have h := congrArg (fun M => M (Sum.inl x) (Sum.inr (j,t))) he
    simpa [Matrix.mul_apply,compactSuccessorInput,compactSuccessorOutput,Fintype.sum_sum_type] using h
  · intro j t
    have h := congrArg (fun M => M (Sum.inr ()) (Sum.inr (j,t))) he
    simpa [Matrix.mul_apply,compactSuccessorInput,compactSuccessorOutput,Fintype.sum_sum_type] using h

omit [DecidableEq Y] [Fintype J] [DecidableEq J] in

theorem compact_response_recurrence {r : ℕ} (F : J → Matrix Y X ℂ)
    (Q : Matrix X (Fin r) ℂ) (a0 : EuclideanSpace ℂ (Fin r))
    (Ares : J → Matrix (Fin r) (Fin r) ℂ) (a : Matrix X Y ℂ)
    (ha : ∀ j, a*(F j*Q)=Q*Ares j) (j : J) (w : List J) :
    (a*F j).toEuclideanLin (compactResponse Q a0 Ares w)=
      compactResponse Q a0 Ares (j::w) := by
  apply WithLp.ofLp_injective
  simp only [compactResponse,residualCoeff,Matrix.ofLp_toLpLin, Matrix.toLin'_apply,
    Matrix.mulVec_mulVec]
  rw [Matrix.mul_assoc,ha j]

omit [DecidableEq X] [DecidableEq Y] [Fintype J] [DecidableEq J] in

theorem compact_response_collection {r : ℕ} (F : J → Matrix Y X ℂ)
    (Q : Matrix X (Fin r) ℂ) (a0 : EuclideanSpace ℂ (Fin r))
    (Ares : J → Matrix (Fin r) (Fin r) ℂ) (c : Y → ℂ)
    (pRow : J → Fin r → ℂ) (q : NCPoly J)
    (hc : ∀ j t, ∑ y, c y*(F j*Q) y t=pRow j t)
    (hq : ∀ j w, q (j::w)=∑ t, pRow j t*residualCoeff a0 Ares w t)
    (j : J) (w : List J) :
    q (j::w)=∑ x, (∑ y, c y*F j y x)*compactResponse Q a0 Ares w x := by
  let C : Matrix Unit Y ℂ := fun _ y => c y
  have hr : (C*F j)*Q=(fun (_ : Unit) t => pRow j t) := by
    rw [Matrix.mul_assoc]
    ext u t
    exact hc j t
  have hmv := congrArg (fun M : Matrix Unit (Fin r) ℂ =>
    (M.mulVec (residualCoeff a0 Ares w)) ()) hr
  dsimp only at hmv
  rw [← Matrix.mulVec_mulVec] at hmv
  rw [hq]
  exact hmv.symm

omit [Fintype X] [DecidableEq X] [Fintype J] [DecidableEq J] in

theorem compact_response_truncation {r D : ℕ} (Q : Matrix X (Fin r) ℂ)
    (a0 : EuclideanSpace ℂ (Fin r)) (Ares : J → Matrix (Fin r) (Fin r) ℂ)
    (hn : ∀ w : List J, w.length=D → matrixWord Ares w=0) :
    ∀ w, D ≤ w.length → compactResponse Q a0 Ares w=0 := by
  intro w hw
  rw [compactResponse,residualCoeff_truncate a0 Ares D hn w hw,map_zero]

theorem compact_certificate_response : ∀ (X Y J : Type) [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [Fintype J] [DecidableEq J]
    (r D : ℕ) (F : J → Matrix Y X ℂ) (Q : Matrix X (Fin r) ℂ)
    (a0 : EuclideanSpace ℂ (Fin r)) (Ares : J → Matrix (Fin r) (Fin r) ℂ)
    (d : ℂ) (pRow : J → Fin r → ℂ) (q : NCPoly J),
  (∀ j w, q (j::w)=∑ t, pRow j t*residualCoeff a0 Ares w t) →
  (∀ w : List J, w.length=D → matrixWord Ares w=0) →
  ((compactSuccessorInput F Q)ᴴ*compactSuccessorInput F Q -
    (compactSuccessorOutput Q a0 Ares d pRow)ᴴ*
      compactSuccessorOutput Q a0 Ares d pRow).PosSemidef →
  ∃ V : Matrix (X ⊕ Unit) (Y ⊕ Unit) ℂ,
    ‖V‖ ≤ 1 ∧
    V*compactSuccessorInput F Q=compactSuccessorOutput Q a0 Ares d pRow ∧
    (∀ x, V (Sum.inl x) (Sum.inr ())=compactResponse Q a0 Ares [] x) ∧
    V (Sum.inr ()) (Sum.inr ())=d ∧
    (∀ j w, (V.submatrix Sum.inl Sum.inl*F j).toEuclideanLin
      (compactResponse Q a0 Ares w)=compactResponse Q a0 Ares (j::w)) ∧
    (∀ w, D ≤ w.length → compactResponse Q a0 Ares w=0) ∧
    (∀ j w, q (j::w)=∑ x, (∑ y, V (Sum.inr ()) (Sum.inl y)*F j y x)*
      compactResponse Q a0 Ares w x) := by
  intro X Y J _ _ _ _ _ _ r D F Q a0 Ares d pRow q hcoef hn hgram
  obtain ⟨V,hV,he⟩ := Qatlib.Concepts.MpsAdaptation.MpsTransfer.gram_dominated_contraction (compactSuccessorInput F Q)
    (compactSuccessorOutput Q a0 Ares d pRow) hgram
  obtain ⟨hinj,hd,ha,hc⟩ := compact_successor_blocks F Q a0 Ares d pRow V he
  refine ⟨V,hV,he,hinj,hd,?_,compact_response_truncation Q a0 Ares hn,?_⟩
  · exact compact_response_recurrence F Q a0 Ares (V.submatrix Sum.inl Sum.inl) ha
  · exact compact_response_collection F Q a0 Ares (fun y => V (Sum.inr ()) (Sum.inl y))
      pRow q hc hcoef

end Qatlib.Papers.PolyTransform26.ResidualCert
