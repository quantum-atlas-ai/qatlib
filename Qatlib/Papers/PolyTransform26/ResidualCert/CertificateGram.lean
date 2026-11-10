/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PolyTransform26.ResidualCert.CertificateGramData
import Qatlib.Papers.PolyTransform26.ResidualCert.TransferExtraction
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.GramQueryCore.GramRealization
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Foundations.MatrixAlgebra.ResponseAlgebra

namespace Qatlib.Papers.PolyTransform26.ResidualCert
open Matrix
open scoped Kronecker Matrix.Norms.L2Operator ComplexOrder
variable {A B R J M : Type} [Fintype A] [Fintype B] [Fintype R] [Fintype M]
  [DecidableEq B] [DecidableEq M]

omit [Fintype R] [DecidableEq B] in

theorem certificate_stacked_gram (K : Matrix M (B × R) ℂ) (G : Matrix B B ℂ) :
    (certificateStackedFactor K)ᴴ*(G ⊗ₖ (1 : Matrix M M ℂ))*certificateStackedFactor K = certificateGramPullback (Kᴴ*K) G := by
  ext s t
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.kroneckerMap_apply,
    certificateStackedFactor,certificateGramPullback,Fintype.sum_prod_type,Matrix.one_apply,
    Finset.sum_mul,Finset.mul_sum,mul_ite,mul_one,mul_zero]
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  calc
    _ = ∑ b, ∑ a, ∑ m, star (K m (a,s))*G a b*K m (b,t) := by
      apply Finset.sum_congr rfl
      intro b hb
      exact Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ m, star (K m (a,s))*G a b*K m (b,t) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro m hm
      ring

omit [Fintype R] in

theorem certificate_stacked_identity (K : Matrix M (B × R) ℂ) :
    (certificateStackedFactor K)ᴴ*certificateStackedFactor K=certificateGramPullback (Kᴴ*K) 1 := by
  simpa only [Matrix.one_kronecker_one,Matrix.mul_one] using
      certificate_stacked_gram K (1 : Matrix B B ℂ)

omit [DecidableEq B] in

theorem certificate_output_gram {r : ℕ} (Q : Matrix B (Fin r) ℂ)
    (a0 : EuclideanSpace ℂ (Fin r)) (Ares : J → Matrix (Fin r) (Fin r) ℂ)
    (d : ℂ) (p : J → Fin r → ℂ) :
    (compactSuccessorOutput Q a0 Ares d p)ᴴ*compactSuccessorOutput Q a0 Ares d p =
      (certificateResidualColumns a0 Ares)ᴴ*(Qᴴ*Q)*certificateResidualColumns a0 Ares+
      (certificateOutputRow d p)ᴴ*certificateOutputRow d p := by
  have he : compactSuccessorOutput Q a0 Ares d p =
      Matrix.fromRows (Q*certificateResidualColumns a0 Ares) (certificateOutputRow d p) := by
    ext i k
    rcases i with i|i <;> rcases k with k|⟨j,t⟩ <;>
      simp [compactSuccessorOutput,certificateResidualColumns,certificateOutputRow,Matrix.mul_apply,Matrix.mulVec,dotProduct]
  rw [he,Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,Matrix.fromCols_mul_fromRows]
  simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]

omit [DecidableEq B] in

theorem certificate_input_gram {r : ℕ} (F : J → Matrix A B ℂ)
    (K : Matrix M (B × Fin r) ℂ) :
    (compactSuccessorInput (fun j => F j ⊗ₖ (1 : Matrix M M ℂ)) (certificateStackedFactor K))ᴴ *
      compactSuccessorInput (fun j => F j ⊗ₖ (1 : Matrix M M ℂ)) (certificateStackedFactor K) =
    (certificateExternalRow (J := J) (R := Fin r))ᴴ*certificateExternalRow + certificateQueryGram F (Kᴴ*K) := by
  ext i k
  rcases i with i|⟨j,s⟩ <;> rcases k with k|⟨l,t⟩
  · simp [compactSuccessorInput,certificateExternalRow,certificateQueryGram,Matrix.mul_apply,
      Matrix.conjTranspose_apply,Fintype.sum_sum_type]
  · simp [compactSuccessorInput,certificateExternalRow,certificateQueryGram,Matrix.mul_apply,
      Matrix.conjTranspose_apply,Fintype.sum_sum_type]
  · simp [compactSuccessorInput,certificateExternalRow,certificateQueryGram,Matrix.mul_apply,
      Matrix.conjTranspose_apply,Fintype.sum_sum_type]
  · have hh := congrArg (fun N : Matrix (Fin r) (Fin r) ℂ => N s t)
      (certificate_stacked_gram K ((F j)ᴴ*F l))
    have hm : ((F j ⊗ₖ (1 : Matrix M M ℂ))*certificateStackedFactor K)ᴴ *
        ((F l ⊗ₖ (1 : Matrix M M ℂ))*certificateStackedFactor K) =
        (certificateStackedFactor K)ᴴ*(((F j)ᴴ*F l) ⊗ₖ (1 : Matrix M M ℂ))*certificateStackedFactor K := by
      have hmul : ((F j)ᴴ ⊗ₖ (1 : Matrix M M ℂ))*(F l ⊗ₖ (1 : Matrix M M ℂ)) =
          ((F j)ᴴ*F l) ⊗ₖ (1 : Matrix M M ℂ) := by
        rw [← Matrix.mul_kronecker_mul,Matrix.one_mul]
      simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_kronecker,
        Matrix.conjTranspose_one]
      rw [← hmul]
      simp only [Matrix.mul_assoc]
    have he := congrArg (fun N : Matrix (Fin r) (Fin r) ℂ => N s t) hm
    simp only [compactSuccessorInput,certificateExternalRow,certificateQueryGram,Matrix.add_apply,
      Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_sum_type,
      mul_zero,Finset.sum_const_zero,add_zero,zero_add] at *
    exact he.trans hh

theorem certificate_successor_defect {r : ℕ} (F : J → Matrix A B ℂ)
    (T : Matrix (B × Fin r) (B × Fin r) ℂ)
    (a0 : EuclideanSpace ℂ (Fin r)) (Ares : J → Matrix (Fin r) (Fin r) ℂ)
    (d : ℂ) (p : J → Fin r → ℂ) (K : Matrix M (B × Fin r) ℂ) (hK : Kᴴ*K=T) :
    (compactSuccessorInput (fun j => F j ⊗ₖ (1 : Matrix M M ℂ)) (certificateStackedFactor K))ᴴ *
      compactSuccessorInput (fun j => F j ⊗ₖ (1 : Matrix M M ℂ)) (certificateStackedFactor K) -
    (compactSuccessorOutput (certificateStackedFactor K) a0 Ares d p)ᴴ *
      compactSuccessorOutput (certificateStackedFactor K) a0 Ares d p =
    compactSourceCertificate F T a0 Ares d p := by
  rw [certificate_input_gram,certificate_output_gram,certificate_stacked_identity,hK]
  unfold compactSourceCertificate
  abel

theorem source_certificate_response (A B J : Type) [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype J] [DecidableEq J]
    (r D : ℕ) (F : J → Matrix A B ℂ) (T : Matrix (B × Fin r) (B × Fin r) ℂ)
    (a0 : EuclideanSpace ℂ (Fin r)) (Ares : J → Matrix (Fin r) (Fin r) ℂ)
    (d : ℂ) (p : J → Fin r → ℂ) (q : NCPoly J)
    (hT : T.PosSemidef) (hS : (compactSourceCertificate F T a0 Ares d p).PosSemidef)
    (hq : ∀ j w, q (j::w)=∑ t, p j t*residualCoeff a0 Ares w t)
    (hn : ∀ w : List J, w.length=D → matrixWord Ares w=0) :
    ∃ K : Matrix (B × Fin r) (B × Fin r) ℂ, Kᴴ*K=T ∧
    let Q := certificateStackedFactor K
    let Fm := fun j => F j ⊗ₖ (1 : Matrix (B × Fin r) (B × Fin r) ℂ)
    ∃ V : Matrix ((B × (B × Fin r)) ⊕ Unit) ((A × (B × Fin r)) ⊕ Unit) ℂ,
      ‖V‖ ≤ 1 ∧ V*compactSuccessorInput Fm Q=compactSuccessorOutput Q a0 Ares d p ∧
      (∀ x, V (Sum.inl x) (Sum.inr ())=compactResponse Q a0 Ares [] x) ∧
      V (Sum.inr ()) (Sum.inr ())=d ∧
      (∀ j w, (V.submatrix Sum.inl Sum.inl*Fm j).toEuclideanLin
        (compactResponse Q a0 Ares w)=compactResponse Q a0 Ares (j::w)) ∧
      (∀ w, D ≤ w.length → compactResponse Q a0 Ares w=0) ∧
      (∀ j w, q (j::w)=∑ x, (∑ y, V (Sum.inr ()) (Sum.inl y)*Fm j y x)*
        compactResponse Q a0 Ares w x) := by
  obtain ⟨K,hK⟩ :=
      Qatlib.Concepts.GramQueryCore.GramRealization.gram_positive_matrix_actual_factorization
      (B × Fin r) T hT
  refine ⟨K,hK,?_⟩
  apply compact_certificate_response (B × (B × Fin r)) (A × (B × Fin r)) J r D
    (fun j => F j ⊗ₖ (1 : Matrix (B × Fin r) (B × Fin r) ℂ)) (certificateStackedFactor K)
    a0 Ares d p q hq hn
  rw [certificate_successor_defect F T a0 Ares d p K hK]
  exact hS

end Qatlib.Papers.PolyTransform26.ResidualCert
