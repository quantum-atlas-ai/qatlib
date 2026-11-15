/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.GramQueryCore.QfiCompletion.MqfiDilationData
public import Qatlib.Concepts.GramQueryCore.QfiCompletion.MqfiCompletionTools
public import Qatlib.Concepts.GramQueryCore.QfiCompletion.MqfiSeparableOfCompletionDeci
public import Qatlib.Concepts.GramQueryCore.GramRealization.GramQueryRealization

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.EncodingCore Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Qatlib.Concepts.GramQueryCore.QfiCompletion.MqfiNPHard2026

namespace Qatlib.Concepts.GramQueryCore.QfiCompletion

open Qatlib.Foundations.MatrixAlgebra.GramFactor
open scoped Classical BigOperators Matrix

/-- Dilation data for `B` yields an MQFI completion of `B`. -/
theorem mqfiCompletion_of_dilationData {p r q : ℕ}
    (B : Fin p → Matrix (Fin r) (Fin q) ℝ) (h : MqfiDilationData B) : HasMqfiCompletion B := by
  obtain ⟨n,u,lam,hu,hmean,hcov⟩ := h
  let J := Fin r ⊕ Fin (q+n)
  let X := Option (Fin p) × Fin r
  let v : Matrix J X ℝ := fun j x => match x.1 with
    | none => (Pi.single (Sum.inl x.2 : J) (1 : ℝ) : J → ℝ) j
    | some a => match j with
      | Sum.inl _ => 0
      | Sum.inr k => mqfiPadCols (B a) x.2 k
  let w : Matrix J X ℝ := fun j x => match x.1 with
    | none => u j x.2
    | some a => lam a j*u j x.2
  have hgramR : v.transpose*v=w.transpose*w := by
    apply Matrix.ext
    intro x y
    rcases x with ⟨a,s⟩
    rcases y with ⟨b,t⟩
    cases a with
    | none =>
      cases b with
      | none =>
        simp only [Matrix.mul_apply,Matrix.transpose_apply,v,w]
        have hv : (∑ j : J,(Pi.single (Sum.inl s : J) (1 : ℝ) : J → ℝ) j*(Pi.single (Sum.inl t : J) (1 : ℝ) : J → ℝ) j)=if s=t then 1 else 0 := by
          simp [J,Pi.single_apply,mul_ite,eq_comm]
        rw [hv]
        exact (hu s t).symm
      | some b =>
        simp only [Matrix.mul_apply,Matrix.transpose_apply,v,w]
        have hv : (∑ j : J,(Pi.single (Sum.inl s : J) (1 : ℝ) : J → ℝ) j*
          (match j with | Sum.inl _ => 0 | Sum.inr k => mqfiPadCols (B b) t k))=0 := by
          simp [J,Pi.single_apply]
        rw [hv]
        have he : (∑ j : J,u j s*(lam b j*u j t))=∑ j : J,lam b j*u j s*u j t := by
          apply Finset.sum_congr rfl
          intro j _
          ring
        rw [he,hmean b s t]
    | some a =>
      cases b with
      | none =>
        simp only [Matrix.mul_apply,Matrix.transpose_apply,v,w]
        have hv : (∑ j : J,(match j with | Sum.inl _ => 0 | Sum.inr k => mqfiPadCols (B a) s k)*
          (Pi.single (Sum.inl t : J) (1 : ℝ) : J → ℝ) j)=0 := by
          simp [J,Pi.single_apply]
        rw [hv,hmean a s t]
      | some b =>
        simp only [Matrix.mul_apply,Matrix.transpose_apply,v,w]
        have hv : (∑ j : J,(match j with | Sum.inl _ => 0 | Sum.inr k => mqfiPadCols (B a) s k)*
          (match j with | Sum.inl _ => 0 | Sum.inr k => mqfiPadCols (B b) t k))=mqfiBlocks B (a,s) (b,t) := by
          simp only [J,Fintype.sum_sum_type,zero_mul,Finset.sum_const_zero,zero_add]
          have hp := congrFun (congrFun (mqfiPadCols_mul_transpose (n := n) (B a) (B b)) s) t
          exact hp
        rw [hv]
        have he : (∑ j : J,(lam a j*u j s)*(lam b j*u j t))=∑ j : J,lam a j*lam b j*u j s*u j t := by
          apply Finset.sum_congr rfl
          intro j _
          ring
        rw [he,hcov a b s t]
  let V : Matrix J X ℂ := v.map (algebraMap ℝ ℂ)
  let W : Matrix J X ℂ := w.map (algebraMap ℝ ℂ)
  have hgram : V.conjTranspose*V=W.conjTranspose*W := by
    ext x y
    simp only [V,W,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.map_apply]
    change (∑ j : J,star (v j x : ℂ)*(v j y : ℂ))=∑ j : J,star (w j x : ℂ)*(w j y : ℂ)
    simp only [Complex.star_def,Complex.conj_ofReal,← Complex.ofReal_mul,← Complex.ofReal_sum]
    exact congrArg (fun a : ℝ => (a : ℂ)) (congrFun (congrFun hgramR x) y)
  obtain ⟨U,hU,hUV⟩ :=
      Qatlib.Concepts.GramQueryCore.GramRealization.gram_equal_actual_unitary_transport J X V W hgram
  have hleft : U*U.conjTranspose=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hU
  have hright : U.conjTranspose*U=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hU
  let D := fun a : Fin p => Matrix.diagonal (fun j : J => (lam a j : ℂ))
  let C := fun a : Fin p => U.conjTranspose*D a*U
  have hD (a : Fin p) : (D a).IsHermitian := by
    change (Matrix.diagonal (fun j : J => (lam a j : ℂ))).conjTranspose=Matrix.diagonal
        (fun j : J => (lam a j : ℂ))
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    ext j
    simp
  have hC (a : Fin p) : (C a).IsHermitian := by
    change (U.conjTranspose*D a*U).conjTranspose=U.conjTranspose*D a*U
    rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,hD a,Matrix.conjTranspose_conjTranspose]
    exact (Matrix.mul_assoc _ _ _).symm
  have hback : U.conjTranspose*W=V := by
    rw [← hUV,← Matrix.mul_assoc,hright,Matrix.one_mul]
  have himage (a : Fin p) (s : Fin r) (j : J) : C a j (Sum.inl s)=V j (some a,s) := by
    have hCV : C a*V=U.conjTranspose*(D a*W) := by
      dsimp [C]
      rw [Matrix.mul_assoc,Matrix.mul_assoc,hUV]
    calc
      _ = (C a*V) j (none,s) := by
        simp [J,V,v,Matrix.mul_apply,Pi.single_apply,apply_ite]
      _ = (U.conjTranspose*(D a*W)) j (none,s) := by rw [hCV]
      _ = (U.conjTranspose*W) j (some a,s) := by
        change (∑ k : J,U.conjTranspose j k*(D a*W) k (none,s))=
          ∑ k : J,U.conjTranspose j k*W k (some a,s)
        apply Finset.sum_congr rfl
        intro k _
        dsimp only [D]
        rw [Matrix.diagonal_mul]
        simp only [W,w,Matrix.map_apply]
        change _*(((lam a k : ℝ) : ℂ)*(u k s : ℂ))=_*((lam a k*u k s : ℝ) : ℂ)
        rw [Complex.ofReal_mul]
      _ = _ := by rw [hback]
  let K := fun a : Fin p => (C a).submatrix Sum.inr Sum.inr
  have hK (a : Fin p) : (K a).IsHermitian := (hC a).submatrix Sum.inr
  have hcomp (a : Fin p) : mqfiCompletion B K a=C a := by
    apply Matrix.ext
    intro i j
    cases i with
    | inl s =>
      cases j with
      | inl t =>
        rw [himage a t (Sum.inl s)]
        simp [mqfiCompletion,V,v,Matrix.map_apply]
      | inr k =>
        have hh := (hC a).apply (Sum.inl s) (Sum.inr k)
        rw [himage a s (Sum.inr k)] at hh
        rw [← hh]
        simp [mqfiCompletion,V,v,Matrix.map_apply]
    | inr k =>
      cases j with
      | inl s =>
        rw [himage a s (Sum.inr k)]
        simp [mqfiCompletion,V,v,Matrix.map_apply,Matrix.conjTranspose_apply]
      | inr l => rfl
  have hcomm (a b : Fin p) : C a*C b=C b*C a := by
    have hbar : U.conjTranspose.conjTranspose*U.conjTranspose=1 := by
      simpa only [Matrix.conjTranspose_conjTranspose] using hleft
    change (U.conjTranspose*Matrix.diagonal (fun j : J => (lam a j : ℂ))*U)*
      (U.conjTranspose*Matrix.diagonal (fun j : J => (lam b j : ℂ))*U)=_
    have hab := mqfi_spectral_product U.conjTranspose hbar (lam a) (lam b)
    have hba := mqfi_spectral_product U.conjTranspose hbar (lam b) (lam a)
    simp only [Matrix.conjTranspose_conjTranspose] at hab hba
    rw [hab]
    change _=(U.conjTranspose*Matrix.diagonal (fun j : J => (lam b j : ℂ))*U)*
      (U.conjTranspose*Matrix.diagonal (fun j : J => (lam a j : ℂ))*U)
    rw [hba]
    have he : (fun j : J => ((lam a j*lam b j : ℝ) : ℂ))=
        (fun j : J => ((lam b j*lam a j : ℝ) : ℂ)) := by
      ext j
      rw [mul_comm]
    rw [he]
  refine ⟨n,K,hK,?_⟩
  intro a b
  rw [hcomp a,hcomp b]
  exact hcomm a b
end Qatlib.Concepts.GramQueryCore.QfiCompletion
