/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedInstrument.RewindAlgebra.RejectionFailureBoundQuan
import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Mathlib.Analysis.Matrix.Order
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.MixedInstrument.RewindAlgebra
open Qatlib.Concepts.WalkSearch.Spectral

namespace Qatlib.Concepts.QuantumGibbs.RejectionRewind
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

def rewindFailureMap {D : ℕ} (P Q : Operator D) (n : ℕ) :
    Operator D →ₗ[ℂ] Operator D :=
  ∑ s : Fin n → Bool,
    conjBranch (rejectWord P Q n s * (1 - P) * (1 - Q) * P)

def rewindSuccessRoundMap {D : ℕ} (P Q : Operator D) (n : ℕ) :
    Operator D →ₗ[ℂ] Operator D :=
  ∑ s : Fin n → Bool, ∑ b : Bool,
    conjBranch (P * (if b then Q else 1 - Q) * (1 - P) *
      rejectWord P Q n s * (1 - P) * (1 - Q) * P)

def rewindStoppedMap {D : ℕ} (P Q : Operator D) (n : ℕ) :
    Operator D →ₗ[ℂ] Operator D :=
  conjBranch (1 - P) + conjBranch (Q * P) + conjBranch (P * (1 - Q) * P) +
    ∑ j ∈ Finset.range n, rewindSuccessRoundMap P Q j

set_option maxHeartbeats 500000

theorem rewindSuccessRoundMap_cp (D : ℕ) (P Q : Operator D) (n : ℕ) :
    CompletelyPositive (rewindSuccessRoundMap P Q n) := by
  unfold rewindSuccessRoundMap
  apply CompletelyPositive.sum
  intro s _
  apply CompletelyPositive.sum
  intro b _
  exact completelyPositive_conjBranch _

theorem rewindFailureMap_cp (D : ℕ) (P Q : Operator D) (n : ℕ) :
    CompletelyPositive (rewindFailureMap P Q n) := by
  unfold rewindFailureMap
  apply CompletelyPositive.sum
  intro s _
  exact completelyPositive_conjBranch _

theorem rewindStoppedMap_cp (D : ℕ) (P Q : Operator D) (n : ℕ) :
    CompletelyPositive (rewindStoppedMap P Q n) := by
  induction n with
  | zero =>
    simp only [rewindStoppedMap,Finset.range_zero,Finset.sum_empty,add_zero]
    exact ((completelyPositive_conjBranch _).add (completelyPositive_conjBranch _)).add
      (completelyPositive_conjBranch _)
  | succ n ih =>
    have he : rewindStoppedMap P Q (n+1)=rewindStoppedMap P Q n+rewindSuccessRoundMap P Q n := by
      simp only [rewindStoppedMap,Finset.sum_range_succ,add_assoc]
    rw [he]
    exact ih.add (rewindSuccessRoundMap_cp D P Q n)

theorem rewindStoppedMap_succ (D : ℕ) (P Q : Operator D) (n : ℕ) :
    rewindStoppedMap P Q (n+1) = rewindStoppedMap P Q n + rewindSuccessRoundMap P Q n := by
  simp only [rewindStoppedMap,Finset.sum_range_succ,add_assoc]

theorem rewind_projective_trace (D : ℕ) (P : Operator D)
    (hPs : P.IsHermitian) (hPi : P*P=P) (X : Operator D) :
    Matrix.trace (conjBranch P X + conjBranch (1-P) X)=Matrix.trace X := by
  have hNP : (1-P)*(1-P)=1-P := by
    noncomm_ring [hPi]
  have hNPs : (1-P)ᴴ=1-P := by simp [hPs.eq]
  simp only [conjBranch_apply,Matrix.trace_add,hPs.eq,hNPs]
  rw [Matrix.trace_mul_cycle P X P,Matrix.trace_mul_cycle (1-P) X (1-P),hPi,
    hNP,← Matrix.trace_add,← Matrix.add_mul]
  simp

def rewindWordSplit (n : ℕ) : (Fin (n+1) → Bool) ≃ Bool × (Fin n → Bool) where
  toFun s := (s 0,fun j => s j.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv s := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv p := by
    rcases p with ⟨b,s⟩
    rfl

theorem rewind_word_sum_succ {A : Type*} [AddCommMonoid A] (n : ℕ)
    (f : (Fin (n+1) → Bool) → A) :
    (∑ s, f s)=∑ b : Bool, ∑ s : Fin n → Bool, f (Fin.cons b s) := by
  calc
    _ = ∑ p : Bool × (Fin n → Bool), f (Fin.cons p.1 p.2) := by
      apply Fintype.sum_equiv (rewindWordSplit n)
      intro s
      exact congrArg f ((rewindWordSplit n).left_inv s).symm
    _ = _ := Fintype.sum_prod_type _

theorem rewind_word_cons (D n : ℕ) (P Q : Operator D) (b : Bool) (s : Fin n → Bool) :
    rejectWord P Q (n+1) (Fin.cons b s)=rejectRound P Q b*rejectWord P Q n s := by
  simp only [rejectWord,Fin.foldr_succ,Fin.cons_zero,Fin.cons_succ]

theorem rewindFailureMap_succ (D n : ℕ) (P Q : Operator D) :
    rewindFailureMap P Q (n+1)=
      ∑ b : Bool, (conjBranch (rejectRound P Q b)).comp (rewindFailureMap P Q n) := by
  apply LinearMap.ext
  intro X
  simp only [rewindFailureMap,LinearMap.sum_apply,LinearMap.comp_apply,map_sum]
  rw [rewind_word_sum_succ]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro s _
  rw [rewind_word_cons]
  have he : (rejectRound P Q b*rejectWord P Q n s)*(1-P)*(1-Q)*P =
      rejectRound P Q b*(rejectWord P Q n s*(1-P)*(1-Q)*P) := by simp only [Matrix.mul_assoc]
  rw [he,← conjBranch_comp]
  rfl

theorem rewindSuccessRoundMap_comp (D n : ℕ) (P Q : Operator D) :
    rewindSuccessRoundMap P Q n = ∑ b : Bool,
      (conjBranch (P*(if b then Q else 1-Q)*(1-P))).comp (rewindFailureMap P Q n) := by
  apply LinearMap.ext
  intro X
  simp only [rewindSuccessRoundMap,rewindFailureMap,LinearMap.sum_apply,LinearMap.comp_apply,map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro s _
  have he : P*(if b then Q else 1-Q)*(1-P)*rejectWord P Q n s*(1-P)*(1-Q)*P =
      (P*(if b then Q else 1-Q)*(1-P))*(rejectWord P Q n s*(1-P)*(1-Q)*P) := by
    simp only [Matrix.mul_assoc]
  rw [he,← conjBranch_comp]
  rfl

theorem rewindFailureMap_zero (D : ℕ) (P Q : Operator D) :
    rewindFailureMap P Q 0=conjBranch ((1-P)*(1-Q)*P) := by
  simp [rewindFailureMap,rejectWord]

theorem rewind_pending_kraus_support (D n : ℕ) (P Q : Operator D) (hPi : P*P=P)
    (s : Fin n → Bool) :
    (1-P)*(rejectWord P Q n s*(1-P)*(1-Q)*P)=rejectWord P Q n s*(1-P)*(1-Q)*P := by
  have hNP : (1-P)*(1-P)=1-P := by noncomm_ring [hPi]
  cases n with
  | zero => simp only [rejectWord,Fin.foldr_zero,Matrix.one_mul,← Matrix.mul_assoc,hNP]
  | succ n =>
    have hw : rejectWord P Q (n+1) s=rejectRound P Q (s 0)*rejectWord P Q n (fun j => s j.succ) := by
      simp only [rejectWord,Fin.foldr_succ]
    have hr : (1-P)*rejectRound P Q (s 0)=rejectRound P Q (s 0) := by
      unfold rejectRound
      rw [← Matrix.mul_assoc,← Matrix.mul_assoc,hNP]
    rw [hw]
    simp only [← Matrix.mul_assoc,hr]

theorem rewind_pending_support (D n : ℕ) (P Q : Operator D) (hPi : P*P=P) (X : Operator D) :
    conjBranch (1-P) (rewindFailureMap P Q n X)=rewindFailureMap P Q n X := by
  have he : (conjBranch (1-P)).comp (rewindFailureMap P Q n)=rewindFailureMap P Q n := by
    unfold rewindFailureMap
    rw [← Module.End.mul_eq_comp,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [Module.End.mul_eq_comp,conjBranch_comp,rewind_pending_kraus_support D n P Q hPi s]
  exact congrArg (fun T : Operator D →ₗ[ℂ] Operator D => T X) he

theorem rewind_conj_mul_apply (D : ℕ) (M N X : Operator D) :
    conjBranch (M*N) X=conjBranch M (conjBranch N X) := by
  rw [← conjBranch_comp]
  rfl

theorem rewind_round_trace (D n : ℕ) (P Q : Operator D)
    (hPs : P.IsHermitian) (hPi : P*P=P) (hQs : Q.IsHermitian) (hQi : Q*Q=Q)
    (X : Operator D) :
    Matrix.trace (rewindSuccessRoundMap P Q n X)+Matrix.trace (rewindFailureMap P Q (n+1) X)=
      Matrix.trace (rewindFailureMap P Q n X) := by
  rw [rewindSuccessRoundMap_comp,rewindFailureMap_succ]
  simp only [LinearMap.sum_apply,LinearMap.comp_apply,Matrix.trace_sum]
  rw [← Finset.sum_add_distrib]
  have hterm (b : Bool) :
      Matrix.trace (conjBranch (P*(if b then Q else 1-Q)*(1-P)) (rewindFailureMap P Q n X))+
        Matrix.trace (conjBranch (rejectRound P Q b) (rewindFailureMap P Q n X)) =
      Matrix.trace (conjBranch (if b then Q else 1-Q) (rewindFailureMap P Q n X)) := by
    simp only [rejectRound,rewind_conj_mul_apply]
    rw [rewind_pending_support D n P Q hPi X]
    simpa only [Matrix.trace_add] using rewind_projective_trace D P hPs hPi
      (conjBranch (if b then Q else 1-Q) (rewindFailureMap P Q n X))
  simp_rw [hterm]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Fintype.sum_bool,← Matrix.trace_add,add_comm] using
    rewind_projective_trace D Q hQs hQi (rewindFailureMap P Q n X)

theorem rewind_initial_trace (D : ℕ) (P Q : Operator D)
    (hPs : P.IsHermitian) (hPi : P*P=P) (hQs : Q.IsHermitian) (hQi : Q*Q=Q)
    (X : Operator D) :
    Matrix.trace (rewindStoppedMap P Q 0 X)+Matrix.trace (rewindFailureMap P Q 0 X)=Matrix.trace X := by
  have hP := rewind_projective_trace D P hPs hPi X
  have hQ := rewind_projective_trace D Q hQs hQi (conjBranch P X)
  have hR := rewind_projective_trace D P hPs hPi (conjBranch (1-Q) (conjBranch P X))
  simp only [Matrix.trace_add] at hP hQ hR
  rw [rewindFailureMap_zero]
  simp only [rewindStoppedMap,Finset.range_zero,Finset.sum_empty,add_zero,
    LinearMap.add_apply,Matrix.trace_add,rewind_conj_mul_apply]
  linear_combination hP+hQ+hR

theorem rewind_finite_trace (D : ℕ) (P Q : Operator D)
    (hPs : P.IsHermitian) (hPi : P*P=P) (hQs : Q.IsHermitian) (hQi : Q*Q=Q)
    (n : ℕ) : TracePreserving (rewindStoppedMap P Q n+rewindFailureMap P Q n) := by
  intro X
  simp only [LinearMap.add_apply,Matrix.trace_add]
  induction n with
  | zero => exact rewind_initial_trace D P Q hPs hPi hQs hQi X
  | succ n ih =>
    rw [rewindStoppedMap_succ,LinearMap.add_apply,Matrix.trace_add]
    have hr := rewind_round_trace D n P Q hPs hPi hQs hQi X
    linear_combination ih+hr

theorem rewindFiniteInstrument :
    ∀ (D : ℕ) (P Q : Operator D),
      P.IsHermitian → P*P=P → Q.IsHermitian → Q*Q=Q → ∀ n : ℕ,
      CompletelyPositive (rewindStoppedMap P Q n) ∧ CompletelyPositive (rewindFailureMap P Q n) ∧
      TracePreserving (rewindStoppedMap P Q n+rewindFailureMap P Q n) ∧
      rewindStoppedMap P Q (n+1)=rewindStoppedMap P Q n+rewindSuccessRoundMap P Q n := by
  intro D P Q hPs hPi hQs hQi n
  exact ⟨rewindStoppedMap_cp D P Q n,rewindFailureMap_cp D P Q n,
    rewind_finite_trace D P Q hPs hPi hQs hQi n,rewindStoppedMap_succ D P Q n⟩

theorem rewind_pure_failure_trace (D n : ℕ) (P Q : Operator D) (ψ : QState (Fin D)) :
    (Matrix.trace (rewindFailureMap P Q n (outerProduct ψ))).re =
      rejectFailProb P Q (P*ᵥψ) n := by
  simp only [rewindFailureMap,LinearMap.sum_apply,Matrix.trace_sum,
    conjBranch_outerProduct,trace_outerProduct,Complex.ofReal_re,
    rejectFailProb,inner_self,← Complex.ofReal_sum,Complex.ofReal_re]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec]

theorem rewind_pure_tail (D n : ℕ) (P Q : Operator D)
    (hPs : P.IsHermitian) (hPi : P*P=P) (hQs : Q.IsHermitian) (hQi : Q*Q=Q)
    (ψ : QState (Fin D)) :
    (Matrix.trace (rewindFailureMap P Q n (outerProduct ψ))).re ≤
      (1/(2*((n:ℝ)+1)))*(Matrix.trace (outerProduct ψ)).re := by
  have hP : IsOrthogonalProjector P := ⟨hPi,hPs⟩
  have hQ : IsOrthogonalProjector Q := ⟨hQi,hQs⟩
  obtain ⟨A,t,hb,hA,hAP,ht⟩ := cs_projector_compressed_eigenframe P Q hP hQ
  have hpψ : P*ᵥ(P*ᵥψ)=P*ᵥψ := by rw [Matrix.mulVec_mulVec,hPi]
  rw [rewind_pure_failure_trace,
    rejection_failure_spectral_formula P Q hQ A t hA hAP ht (P*ᵥψ) hpψ n]
  let z := Aᴴ*ᵥ(P*ᵥψ)
  have hAz : A*ᵥz=P*ᵥψ := by
    change A*ᵥ(Aᴴ*ᵥ(P*ᵥψ))=P*ᵥψ
    rw [Matrix.mulVec_mulVec,hAP,hpψ]
  have hz : ∑ i, ‖z i‖^2=(Matrix.trace (outerProduct (P*ᵥψ))).re := by
    have he := Qatlib.Concepts.BlockEncoding.Postselection.Encoding.IsIsometry.inner_mulVec hA z z
    change Qatlib.Foundations.PureStateMath.Inner (A*ᵥz)
        (A*ᵥz)=Qatlib.Foundations.PureStateMath.Inner z z at he
    rw [hAz] at he
    have hr := congrArg Complex.re he
    simp only [inner_self,← Complex.ofReal_sum,Complex.ofReal_re] at hr
    simpa only [trace_outerProduct,Complex.ofReal_re] using hr.symm
  have hcontract : (Matrix.trace (outerProduct (P*ᵥψ))).re ≤
      (Matrix.trace (outerProduct ψ)).re := by
    have he := congrArg Complex.re (rewind_projective_trace D P hPs hPi (outerProduct ψ))
    simp only [Matrix.trace_add,Complex.add_re,conjBranch_outerProduct] at he
    have hn := (outerProduct_posSemidef ((1-P)*ᵥψ)).trace_nonneg
    have hn' : 0 ≤ (Matrix.trace (outerProduct ((1-P)*ᵥψ))).re :=
      (Complex.nonneg_iff.mp hn).1
    linarith
  calc
    _ ≤ ∑ i, (1/(2*((n:ℝ)+1)))*‖z i‖^2 := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (rejection_scalar_bound (t i) (hb i) n) (sq_nonneg _)
    _ = (1/(2*((n:ℝ)+1)))*(Matrix.trace (outerProduct (P*ᵥψ))).re := by
      rw [← Finset.mul_sum,hz]
    _ ≤ _ := mul_le_mul_of_nonneg_left hcontract (by positivity)

theorem rewind_psd_columns (D : ℕ) (X : Operator D) (hX : X.PosSemidef) :
    ∃ ψ : Fin D → QState (Fin D), X=∑ j, outerProduct (ψ j) := by
  let B : Operator D := CFC.sqrt X
  have hB : B.PosSemidef := (CFC.sqrt_nonneg X).posSemidef
  have hBB : B*Bᴴ=X := by
    rw [hB.isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self X hX.nonneg
  refine ⟨fun j i => B i j,?_⟩
  rw [← hBB]
  ext i k
  simp [Matrix.mul_apply,outerProduct,Matrix.conjTranspose_apply,Matrix.sum_apply]

theorem rewind_psd_tail (D n : ℕ) (P Q : Operator D)
    (hPs : P.IsHermitian) (hPi : P*P=P) (hQs : Q.IsHermitian) (hQi : Q*Q=Q)
    (X : Operator D) (hX : X.PosSemidef) :
    (Matrix.trace (rewindFailureMap P Q n X)).re ≤
      (1/(2*((n:ℝ)+1)))*(Matrix.trace X).re := by
  obtain ⟨ψ,rfl⟩ := rewind_psd_columns D X hX
  simp only [map_sum,Matrix.trace_sum,Complex.re_sum]
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => rewind_pure_tail D n P Q hPs hPi hQs hQi (ψ j)

theorem rewindMixedTail :
    ∀ (D : ℕ) (P Q : Operator D),
      P.IsHermitian → P*P=P → Q.IsHermitian → Q*Q=Q →
      ∀ ρ : Operator D, ρ.PosSemidef → Matrix.trace ρ=1 → ∀ n : ℕ,
        (Matrix.trace (rewindFailureMap P Q n ρ)).re ≤ 1/(2*((n:ℝ)+1)) := by
  intro D P Q hPs hPi hQs hQi ρ hρ htr n
  simpa only [htr,Complex.one_re,mul_one] using rewind_psd_tail D n P Q hPs hPi hQs hQi ρ hρ

end Qatlib.Concepts.QuantumGibbs.RejectionRewind
