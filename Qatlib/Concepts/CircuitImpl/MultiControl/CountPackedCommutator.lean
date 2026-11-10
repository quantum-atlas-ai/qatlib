/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.MultiControl.CountFramedBorrowed
import Qatlib.Concepts.CircuitImpl.MultiControl.CountCommutators
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.CircuitImpl.MultiControl
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.CircuitImpl.MultiControl.CountPackedCommutator
open Matrix
open scoped Classical BigOperators

def sourcePackedCommutator {N : ℕ} (s t : Fin N) (R E : Matrix Bool Bool ℂ)
    (as bs : List (ReflectionGate N)) : List (ReflectionGate N) :=
  [.inl (t,Hadamard), .inl (s,R)] ++ as ++ [.inl (s,E*Rᴴ)] ++ bs ++
    [.inl (s,R*Eᴴ)] ++ reflectionAdjoint as ++ [.inl (s,E*Rᴴ)] ++ reflectionAdjoint bs ++
    [.inl (s,Eᴴ), .inl (t,Hadamard)]

theorem sourcePackedCommutator_length {N : ℕ} (s t : Fin N) (R E : Matrix Bool Bool ℂ)
    (as bs : List (ReflectionGate N)) :
    (sourcePackedCommutator s t R E as bs).length = 2*as.length+2*bs.length+7 := by
  simp only [sourcePackedCommutator, List.length_append, List.length_cons, List.length_nil,
    reflectionAdjoint_length]
  omega

private theorem singleton_legal {N : ℕ} (s : Fin N) (U : Matrix Bool Bool ℂ)
    (hU : U ∈ unitaryGroup Bool ℂ) : reflectionLegal [.inl (s,U)] := by
  simpa [reflectionLegal, reflectionGateLegal] using! hU

theorem sourcePackedCommutator_legal {N : ℕ} (s t : Fin N) (R E : Matrix Bool Bool ℂ)
    (hR : R ∈ unitaryGroup Bool ℂ) (hE : E ∈ unitaryGroup Bool ℂ)
    (as bs : List (ReflectionGate N)) (has : reflectionLegal as) (hbs : reflectionLegal bs) :
    reflectionLegal (sourcePackedCommutator s t R E as bs) := by
  have hS :=
      singleton_legal s (E*Rᴴ)
      ((unitaryGroup Bool ℂ).mul_mem hE (Qatlib.Concepts.Execution.WorkspaceCP.adjoint_unitary hR))
  have hT :=
      singleton_legal s (R*Eᴴ)
      ((unitaryGroup Bool ℂ).mul_mem hR (Qatlib.Concepts.Execution.WorkspaceCP.adjoint_unitary hE))
  have hfront : reflectionLegal [.inl (t,Hadamard), .inl (s,R)] := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact hadamard_unitary
    · exact hR
  have hback : reflectionLegal [.inl (s,Eᴴ), .inl (t,Hadamard)] := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact Qatlib.Concepts.Execution.WorkspaceCP.adjoint_unitary hE
    · exact hadamard_unitary
  have haa := reflectionAdjoint_legal as has
  have hba := reflectionAdjoint_legal bs hbs
  simp only [sourcePackedCommutator, reflectionLegal_append]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨hfront,has⟩,hS⟩,hbs⟩,hT⟩,haa⟩,hS⟩,hba⟩,hback⟩

private theorem packing_algebra {I : Type} [Fintype I] [DecidableEq I]
    (P Q E D H A B : Matrix I I ℂ)
    (hP : H*P=P*H) (hQ : H*Q=Q*H) (hE : H*E=E*H) (hD : H*D=D*H)
    (hA : H*A=A*H) (hAa : H*Aᴴ=Aᴴ*H) (hHH : H*H=1) :
    (H*D)*Bᴴ*(E*Q)*Aᴴ*(P*D)*B*(E*Q)*A*(P*H) =
      (D*(H*(Bᴴ*(H*E))))*((Q*(Aᴴ*P))*((D*(H*(B*(H*E))))*(Q*(A*P)))) := by
  have moveP (Z : Matrix I I ℂ) : H*(P*Z)=P*(H*Z) := by
    rw [← Matrix.mul_assoc, hP, Matrix.mul_assoc]
  have moveQ (Z : Matrix I I ℂ) : H*(Q*Z)=Q*(H*Z) := by
    rw [← Matrix.mul_assoc, hQ, Matrix.mul_assoc]
  have moveE (Z : Matrix I I ℂ) : H*(E*Z)=E*(H*Z) := by
    rw [← Matrix.mul_assoc, hE, Matrix.mul_assoc]
  have moveD (Z : Matrix I I ℂ) : H*(D*Z)=D*(H*Z) := by
    rw [← Matrix.mul_assoc, hD, Matrix.mul_assoc]
  have moveA (Z : Matrix I I ℂ) : H*(A*Z)=A*(H*Z) := by
    rw [← Matrix.mul_assoc, hA, Matrix.mul_assoc]
  have moveAa (Z : Matrix I I ℂ) : H*(Aᴴ*Z)=Aᴴ*(H*Z) := by
    rw [← Matrix.mul_assoc, hAa, Matrix.mul_assoc]
  have cancel (Z : Matrix I I ℂ) : H*(H*Z)=Z := by rw [← Matrix.mul_assoc, hHH, Matrix.one_mul]
  have middle (Z : Matrix I I ℂ) : H*(E*(Q*(Aᴴ*(P*(D*(H*Z)))))) = E*(Q*(Aᴴ*(P*(D*Z)))) := by
    simp only [moveE,moveQ,moveAa,moveP,moveD,cancel]
  have rightSide : H*(E*(Q*(A*P))) = E*(Q*(A*(P*H))) := by
    simp only [moveE,moveQ,moveA]
    rw [hP]
  have leftSide (Z : Matrix I I ℂ) : D*(H*Z)=H*(D*Z) := by
    rw [← Matrix.mul_assoc, ← hD, Matrix.mul_assoc]
  simp only [Matrix.mul_assoc]
  rw [middle, rightSide, leftSide]

private theorem singleton_matrix {N : ℕ} (g : ReflectionGate N) :
    reflectionProgramMatrix [g] = reflectionGateMatrix g := by simp [reflectionProgramMatrix]

theorem sourcePackedCommutator_matrix {N : ℕ} (s t : Fin N) (hst : s ≠ t)
    (R E : Matrix Bool Bool ℂ) (hR : R ∈ unitaryGroup Bool ℂ) (hE : E ∈ unitaryGroup Bool ℂ)
    (as bs : List (ReflectionGate N)) (has : reflectionLegal as) (hbs : reflectionLegal bs)
    (hav : ∀ g ∈ as, t ∉ reflectionGateWires g) :
    let af := [.inl (s,R)] ++ as ++ [.inl (s,Rᴴ)]
    let bf := [.inl (s,E), .inl (t,Hadamard)] ++ bs ++ [.inl (t,Hadamard), .inl (s,Eᴴ)]
    reflectionProgramMatrix (sourcePackedCommutator s t R E as bs) =
      reflectionProgramMatrix (af ++ bf ++ reflectionAdjoint af ++ reflectionAdjoint bf) := by
  (try dsimp only)
  let P := wireGate N s R
  let Q := wireGate N s Rᴴ
  let W := wireGate N s E
  let D := wireGate N s Eᴴ
  let H := wireGate N t Hadamard
  let A := reflectionProgramMatrix as
  let B := reflectionProgramMatrix bs
  let af : List (ReflectionGate N) := [.inl (s,R)] ++ as ++ [.inl (s,Rᴴ)]
  let bf : List (ReflectionGate N) :=
      [.inl (s,E), .inl (t,Hadamard)] ++ bs ++ [.inl (t,Hadamard), .inl (s,Eᴴ)]
  have haf : reflectionLegal af := by
    simp only [af, reflectionLegal_append]
    exact ⟨⟨singleton_legal s R hR,has⟩,singleton_legal s Rᴴ (Qatlib.Concepts.Execution.WorkspaceCP.adjoint_unitary hR)⟩
  have hbf : reflectionLegal bf := by
    have hfront : reflectionLegal [.inl (s,E), .inl (t,Hadamard)] := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact hE
      · exact hadamard_unitary
    have hback : reflectionLegal [.inl (t,Hadamard), .inl (s,Eᴴ)] := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact hadamard_unitary
      · exact Qatlib.Concepts.Execution.WorkspaceCP.adjoint_unitary hE
    simp only [bf, reflectionLegal_append]
    exact ⟨⟨hfront,hbs⟩,hback⟩
  have hP : H*P=P*H := (source_wireGate_commute s t hst R Hadamard).symm
  have hQ : H*Q=Q*H := (source_wireGate_commute s t hst Rᴴ Hadamard).symm
  have hW : H*W=W*H := (source_wireGate_commute s t hst E Hadamard).symm
  have hD : H*D=D*H := (source_wireGate_commute s t hst Eᴴ Hadamard).symm
  have hA : H*A=A*H := source_wireGate_commute_table t Hadamard as has hav
  have hAa : H*Aᴴ=Aᴴ*H := by
    have hh := source_wireGate_commute_table t Hadamard (reflectionAdjoint as)
      (reflectionAdjoint_legal as has) (source_adjoint_avoids as t hav)
    rwa [reflectionAdjoint_matrix as has] at hh
  have hHH : H*H=1 := by dsimp only [H]; rw [wireGate_mul, hadamard_mul_self, wireGate_one]
  have hHS : Hᴴ=H := by dsimp only [H]; rw [wireGate_conjTranspose, hadamard_conjTranspose]
  have hPS : Pᴴ=Q := wireGate_conjTranspose N s R
  have hQS : Qᴴ=P := by
    dsimp only [Q,P]; rw [wireGate_conjTranspose, Matrix.conjTranspose_conjTranspose]
  have hWS : Wᴴ=D := wireGate_conjTranspose N s E
  have hDS : Dᴴ=W := by
    dsimp only [D,W]; rw [wireGate_conjTranspose, Matrix.conjTranspose_conjTranspose]
  have hAM : reflectionProgramMatrix af=Q*(A*P) := by
    rw [show af=[.inl (s,R)] ++ as ++ [.inl (s,Rᴴ)] from rfl,
      reflectionProgramMatrix_append, reflectionProgramMatrix_append]
    simp only [singleton_matrix, reflectionGateMatrix]
    rfl
  have hfront : reflectionProgramMatrix [.inl (s,E), .inl (t,Hadamard)] = H*W := by
    simp only [reflectionProgramMatrix, reflectionGateMatrix, Matrix.one_mul]
    rfl
  have hback : reflectionProgramMatrix [.inl (t,Hadamard), .inl (s,Eᴴ)] = D*H := by
    simp only [reflectionProgramMatrix, reflectionGateMatrix, Matrix.one_mul]
    rfl
  have hBM : reflectionProgramMatrix bf=D*(H*(B*(H*W))) := by
    rw [show bf=[.inl (s,E), .inl (t,Hadamard)] ++ bs ++ [.inl (t,Hadamard), .inl (s,Eᴴ)] from rfl,
      reflectionProgramMatrix_append, reflectionProgramMatrix_append, hfront, hback]
    simp only [Matrix.mul_assoc]
    rfl
  have hAMA : reflectionProgramMatrix (reflectionAdjoint af)=Q*(Aᴴ*P) := by
    rw [reflectionAdjoint_matrix af haf, hAM, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        hPS, hQS]
    simp only [Matrix.mul_assoc]
  have hBMA : reflectionProgramMatrix (reflectionAdjoint bf)=D*(H*(Bᴴ*(H*W))) := by
    rw [reflectionAdjoint_matrix bf hbf, hBM, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hWS, hDS, hHS]
    simp only [Matrix.mul_assoc]
  have hquad : reflectionProgramMatrix (af ++ bf ++ reflectionAdjoint af ++ reflectionAdjoint bf) =
      (D*(H*(Bᴴ*(H*W))))*((Q*(Aᴴ*P))*((D*(H*(B*(H*W))))*(Q*(A*P)))) := by
    rw [reflectionProgramMatrix_append, reflectionProgramMatrix_append, reflectionProgramMatrix_append,
      hAM, hBM, hAMA, hBMA]
  have hpFront : reflectionProgramMatrix [.inl (t,Hadamard), .inl (s,R)] = P*H := by
    simp only [reflectionProgramMatrix, reflectionGateMatrix, Matrix.one_mul]
    rfl
  have hpBack : reflectionProgramMatrix [.inl (s,Eᴴ), .inl (t,Hadamard)] = H*D := by
    simp only [reflectionProgramMatrix, reflectionGateMatrix, Matrix.one_mul]
    rfl
  have hS : reflectionProgramMatrix [.inl (s,E*Rᴴ)] = W*Q := by
    rw [singleton_matrix]
    exact (wireGate_mul N s E Rᴴ).symm
  have hT : reflectionProgramMatrix [.inl (s,R*Eᴴ)] = P*D := by
    rw [singleton_matrix]
    exact (wireGate_mul N s R Eᴴ).symm
  have hpacked : reflectionProgramMatrix (sourcePackedCommutator s t R E as bs) =
      (H*D)*Bᴴ*(W*Q)*Aᴴ*(P*D)*B*(W*Q)*A*(P*H) := by
    rw [sourcePackedCommutator, reflectionProgramMatrix_append, reflectionProgramMatrix_append,
      reflectionProgramMatrix_append, reflectionProgramMatrix_append, reflectionProgramMatrix_append,
      reflectionProgramMatrix_append, reflectionProgramMatrix_append, reflectionProgramMatrix_append,
      hpFront, hpBack, hS, hT, reflectionAdjoint_matrix as has, reflectionAdjoint_matrix bs hbs]
    simp only [Matrix.mul_assoc]
    rfl
  exact hpacked.trans ((packing_algebra P Q W D H A B hP hQ hW hD hA hAa hHH).trans hquad.symm)

end Qatlib.Concepts.CircuitImpl.MultiControl.CountPackedCommutator
