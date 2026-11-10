/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.MultiControl.CountBorrowed
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.CircuitImpl.MultiControl
open Qatlib.Concepts.CircuitImpl.MultiControl.CountCompressedLadders
open Qatlib.Concepts.CircuitImpl.MultiControl.CountToffoliFrames
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.CircuitImpl.MultiControl.CountFramedBorrowed
open Matrix
open scoped Classical BigOperators

def sourceBorrowedRelativeCore {N : ℕ} (c w : ℕ → Fin N) (s : Fin N) (r : ℕ) : List (ReflectionGate N) :=
  let g := sourceRelativeMiddle (c (r+1)) (w (r-1)) s;
  let F := sourcePrefixCompressed c w r;
  g ++ F ++ g ++ F

def sourceBorrowedExactCore {N : ℕ} (c w : ℕ → Fin N) (t : Fin N) (r : ℕ) : List (ReflectionGate N) :=
  let g := sourceToffoliMiddle (c (r+1)) (w (r-1)) t;
  let F := sourcePrefixCompressed c w r;
  g ++ F ++ reflectionAdjoint g ++ F

theorem sourceBorrowedCore_lengths {N : ℕ} (c w : ℕ → Fin N) (s t : Fin N) (r : ℕ) (hr : 1 ≤ r) :
    (sourceBorrowedRelativeCore c w s r).length = 24*r ∧
    (sourceBorrowedExactCore c w t r).length = 24*r+14 := by
  have hF := sourcePrefixCompressed_length c w r hr
  have hm : (sourceRelativeMiddle (c (r+1)) (w (r-1)) s).length = 5 := rfl
  have ht : (sourceToffoliMiddle (c (r+1)) (w (r-1)) t).length = 12 := rfl
  constructor
  · simp only [sourceBorrowedRelativeCore, List.length_append, hm, hF]
    omega
  · simp only [sourceBorrowedExactCore, List.length_append, reflectionAdjoint_length, ht, hF]
    omega

private theorem singleton_matrix {N : ℕ} (g : ReflectionGate N) :
    reflectionProgramMatrix [g] = reflectionGateMatrix g := by simp [reflectionProgramMatrix]

private theorem relative_frame_algebra {I : Type} [Fintype I] [DecidableEq I]
    (R S K F : Matrix I I ℂ) (hS : S*F=F*S) (hRS : R*S=1) :
    S*(F*(K*(F*(K*R)))) = F*((S*(K*R))*(F*(S*(K*R)))) := by
  have hFS (D : Matrix I I ℂ) : F*(S*D)=S*(F*D) := by
    rw [← Matrix.mul_assoc, ← hS, Matrix.mul_assoc]
  have hcancel (D : Matrix I I ℂ) : R*(S*D)=D := by
    rw [← Matrix.mul_assoc, hRS, Matrix.one_mul]
  simp only [Matrix.mul_assoc, hFS, hcancel]

private theorem exact_frame_algebra {I : Type} [Fintype I] [DecidableEq I]
    (E S H K F : Matrix I I ℂ) (hH : H*F=F*H) (hS : S*F=F*S) (hHH : H*H=1) :
    S*(H*(F*(Kᴴ*(F*(K*(H*E)))))) =
      F*((S*(H*(Kᴴ*H)))*(F*(H*(K*(H*E))))) := by
  have hcancel (D : Matrix I I ℂ) : H*(H*D)=D := by
    rw [← Matrix.mul_assoc, hHH, Matrix.one_mul]
  have hFS (D : Matrix I I ℂ) : F*(S*D)=S*(F*D) := by
    rw [← Matrix.mul_assoc, ← hS, Matrix.mul_assoc]
  have hFH (D : Matrix I I ℂ) : F*(H*D)=H*(F*D) := by
    rw [← Matrix.mul_assoc, ← hH, Matrix.mul_assoc]
  simp only [Matrix.mul_assoc, hFS, hFH, hcancel]

theorem sourceBorrowedRelative_frame {N : ℕ} (c w : ℕ → Fin N) (s : Fin N) (r : ℕ)
    (h : noWorkDirtyPrefixLayout c w r)
    (hc : ∀ i < r+1, c i ≠ s) (hw : ∀ j < r, w j ≠ s) :
    reflectionProgramMatrix
      ([.inl (s,qubitEulerRotation (-Real.pi/4))] ++ sourceBorrowedRelativeCore c w s r ++
        [.inl (s,(qubitEulerRotation (-Real.pi/4))ᴴ)]) =
      reflectionProgramMatrix (sourceBorrowedRelative c w s r) := by
  let R := wireGate N s (qubitEulerRotation (-Real.pi/4))
  let S := wireGate N s ((qubitEulerRotation (-Real.pi/4))ᴴ)
  let K := reflectionProgramMatrix (sourceRelativeMiddle (c (r+1)) (w (r-1)) s)
  let F := reflectionProgramMatrix (sourcePrefixCompressed c w r)
  let G := reflectionProgramMatrix (sourceRelativeToffoliSteps (c (r+1)) (w (r-1)) s)
  have hS : S*F=F*S := sourcePrefixCompressed_wire_commute c w r h s _
    (fun i hi => (hc i hi).symm) (fun j hj => (hw j hj).symm)
  have hRS : R*S=1 := by
    dsimp only [R,S]
    rw [wireGate_mul]
    have hu : qubitEulerRotation (-Real.pi/4) * (qubitEulerRotation (-Real.pi/4))ᴴ=1 := by
      simpa only [Matrix.star_eq_conjTranspose] using!
          Matrix.mem_unitaryGroup_iff.mp (qubitEulerRotation_unitary (-Real.pi/4))
    rw [hu, wireGate_one]
  have hG : G=S*(K*R) := by
    have hg : sourceRelativeToffoliSteps (c (r+1)) (w (r-1)) s =
        [.inl (s,qubitEulerRotation (-Real.pi/4))] ++ sourceRelativeMiddle (c (r+1)) (w (r-1)) s ++
        [.inl (s,(qubitEulerRotation (-Real.pi/4))ᴴ)] := rfl
    dsimp only [G]
    rw [hg]
    simp only [reflectionProgramMatrix_append, singleton_matrix, reflectionGateMatrix,
        Matrix.mul_assoc]
    rfl
  have hcore : reflectionProgramMatrix (sourceBorrowedRelativeCore c w s r) = F*(K*(F*K)) := by
    rw [sourceBorrowedRelativeCore]
    simp only [reflectionProgramMatrix_append, Matrix.mul_assoc]
    rfl
  have hraw : reflectionProgramMatrix (sourceBorrowedRelative c w s r)=F*(G*(F*G)) := by
    rw [sourceBorrowedRelative]
    simp only [reflectionProgramMatrix_append, Matrix.mul_assoc]
    rfl
  have houter : reflectionProgramMatrix
      ([.inl (s,qubitEulerRotation (-Real.pi/4))] ++ sourceBorrowedRelativeCore c w s r ++
        [.inl (s,(qubitEulerRotation (-Real.pi/4))ᴴ)]) =
      S*(reflectionProgramMatrix (sourceBorrowedRelativeCore c w s r)*R) := by
    rw [reflectionProgramMatrix_append, reflectionProgramMatrix_append]
    simp only [singleton_matrix, reflectionGateMatrix]
    rfl
  calc
    _ = S*(reflectionProgramMatrix (sourceBorrowedRelativeCore c w s r)*R) := houter
    _ = S*(F*(K*(F*(K*R)))) := by
      simpa only [Matrix.mul_assoc] using!
          congrArg (fun Q : Matrix (Reg N) (Reg N) ℂ => S*(Q*R)) hcore
    _ = F*((S*(K*R))*(F*(S*(K*R)))) := relative_frame_algebra R S K F hS hRS
    _ = F*(G*(F*G)) := congrArg (fun Q : Matrix (Reg N) (Reg N) ℂ => F*(Q*(F*Q))) hG.symm
    _ = _ := hraw.symm

theorem sourceBorrowedExact_frame {N : ℕ} (c w : ℕ → Fin N) (t : Fin N) (r : ℕ)
    (hr : 1 ≤ r) (h : noWorkDirtyPrefixLayout c w r)
    (hlast : ∀ j < r, c (r+1) ≠ w j)
    (hfirst : ∀ i < r+1, c (r+1) ≠ c i)
    (hc : ∀ i < r+2, c i ≠ t) (hw : ∀ j < r, w j ≠ t) :
    reflectionProgramMatrix
      ([.inl (c (r+1),tGate), .inl (t,Hadamard)] ++ sourceBorrowedExactCore c w t r ++
        [.inl (t,Hadamard), .inl (c (r+1),tGateᴴ)]) =
      reflectionProgramMatrix (sourceBorrowedExact c w t r) := by
  let a := c (r+1)
  let b := w (r-1)
  let E := wireGate N a tGate
  let S := wireGate N a tGateᴴ
  let H := wireGate N t Hadamard
  let K := reflectionProgramMatrix (sourceToffoliMiddle a b t)
  let F := reflectionProgramMatrix (sourcePrefixCompressed c w r)
  let T := reflectionProgramMatrix (sourceToffoliFramed a b t)
  have hgt : reflectionLegal (sourceToffoliFramed a b t) := sourceToffoliFramed_legal a b t
    (hlast _ (by omega)) (hc _ (by omega)) (hw _ (by omega))
  have hkt : reflectionLegal (sourceToffoliMiddle a b t) := sourceToffoliMiddle_legal a b t
    (hlast _ (by omega)) (hc _ (by omega)) (hw _ (by omega))
  have hS : S*F=F*S := sourcePrefixCompressed_wire_commute c w r h a _ hfirst hlast
  have hH : H*F=F*H := sourcePrefixCompressed_wire_commute c w r h t _
    (fun i hi => (hc i (by omega)).symm) (fun j hj => (hw j hj).symm)
  have hHS : Hᴴ=H := by dsimp only [H]; rw [wireGate_conjTranspose, hadamard_conjTranspose]
  have hES : Eᴴ=S := wireGate_conjTranspose N a tGate
  have hHH : H*H=1 := by dsimp only [H]; rw [wireGate_mul, hadamard_mul_self, wireGate_one]
  have hfront : reflectionProgramMatrix [.inl (a,tGate), .inl (t,Hadamard)] = H*E := by
    simp only [reflectionProgramMatrix, reflectionGateMatrix, Matrix.one_mul]
    rfl
  have hback : reflectionProgramMatrix [.inl (t,Hadamard), .inl (a,tGateᴴ)] = S*H := by
    simp only [reflectionProgramMatrix, reflectionGateMatrix, Matrix.one_mul]
    rfl
  have hT : T=H*(K*(H*E)) := by
    dsimp only [T]
    rw [sourceToffoliFramed, reflectionProgramMatrix_append, reflectionProgramMatrix_append]
    simp only [hfront, singleton_matrix, reflectionGateMatrix]
    rfl
  have hTa : Tᴴ=S*(H*(Kᴴ*H)) := by
    rw [hT, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hHS, hES]
    simp only [Matrix.mul_assoc]
  have hcore : reflectionProgramMatrix (sourceBorrowedExactCore c w t r)=F*(Kᴴ*(F*K)) := by
    rw [sourceBorrowedExactCore]
    rw [reflectionProgramMatrix_append, reflectionProgramMatrix_append, reflectionProgramMatrix_append,
      reflectionAdjoint_matrix _ hkt]
  have hraw : reflectionProgramMatrix (sourceBorrowedExact c w t r)=F*(Tᴴ*(F*T)) := by
    rw [sourceBorrowedExact]
    rw [reflectionProgramMatrix_append, reflectionProgramMatrix_append, reflectionProgramMatrix_append,
      reflectionAdjoint_matrix _ hgt]
  have houter : reflectionProgramMatrix
      ([.inl (a,tGate), .inl (t,Hadamard)] ++ sourceBorrowedExactCore c w t r ++
        [.inl (t,Hadamard), .inl (a,tGateᴴ)]) =
      S*(H*(reflectionProgramMatrix (sourceBorrowedExactCore c w t r)*(H*E))) := by
    rw [reflectionProgramMatrix_append, reflectionProgramMatrix_append, hfront, hback]
    simp only [Matrix.mul_assoc]
  calc
    _ = S*(H*(reflectionProgramMatrix (sourceBorrowedExactCore c w t r)*(H*E))) := houter
    _ = S*(H*(F*(Kᴴ*(F*(K*(H*E)))))) := by
      simpa only [Matrix.mul_assoc] using!
        congrArg (fun Q : Matrix (Reg N) (Reg N) ℂ => S*(H*(Q*(H*E)))) hcore
    _ = F*((S*(H*(Kᴴ*H)))*(F*(H*(K*(H*E))))) := exact_frame_algebra E S H K F hH hS hHH
    _ = F*(Tᴴ*(F*T)) := by
      exact congrArg₂ (fun Q P : Matrix (Reg N) (Reg N) ℂ => F*(Q*(F*P))) hTa.symm hT.symm
    _ = _ := hraw.symm

theorem sourceBorrowedRelativeCore_legal {N : ℕ} (c w : ℕ → Fin N) (s : Fin N) (r : ℕ)
    (hr : 1 ≤ r) (h : noWorkDirtyPrefixLayout c w r)
    (hc : ∀ i < r+2, c i ≠ s) (hw : ∀ j < r, w j ≠ s) :
    reflectionLegal (sourceBorrowedRelativeCore c w s r) := by
  have hg := sourceRelativeMiddle_legal (c (r+1)) (w (r-1)) s (hc _ (by omega)) (hw _ (by omega))
  have hF := sourcePrefixCompressed_legal c w r h
  simp only [sourceBorrowedRelativeCore, reflectionLegal_append]
  exact ⟨⟨⟨hg,hF⟩,hg⟩,hF⟩

theorem sourceBorrowedExactCore_legal {N : ℕ} (c w : ℕ → Fin N) (t : Fin N) (r : ℕ)
    (hr : 1 ≤ r) (h : noWorkDirtyPrefixLayout c w r)
    (hlast : ∀ j < r, c (r+1) ≠ w j)
    (hc : ∀ i < r+2, c i ≠ t) (hw : ∀ j < r, w j ≠ t) :
    reflectionLegal (sourceBorrowedExactCore c w t r) := by
  have hg := sourceToffoliMiddle_legal (c (r+1)) (w (r-1)) t
    (hlast _ (by omega)) (hc _ (by omega)) (hw _ (by omega))
  have hF := sourcePrefixCompressed_legal c w r h
  have hga := reflectionAdjoint_legal _ hg
  simp only [sourceBorrowedExactCore, reflectionLegal_append]
  exact ⟨⟨⟨hg,hF⟩,hga⟩,hF⟩

theorem sourceBorrowedRelativeCore_avoids {N : ℕ} (c w : ℕ → Fin N) (s z : Fin N) (r : ℕ)
    (hr : 1 ≤ r) (hc : ∀ i < r+2, z ≠ c i) (hw : ∀ j < r, z ≠ w j) (hs : z ≠ s) :
    ∀ g ∈ sourceBorrowedRelativeCore c w s r, z ∉ reflectionGateWires g := by
  have hg :=
      sourceRelativeMiddle_avoids (c (r+1)) (w (r-1)) s z (hc _ (by omega)) (hw _ (by omega)) hs
  have hF := sourcePrefixCompressed_avoids c w r z (fun i hi => hc i (by omega)) hw
  intro g hm
  simp only [sourceBorrowedRelativeCore, List.mem_append] at hm
  rcases hm with ((hm | hm) | hm) | hm
  · exact hg g hm
  · exact hF g hm
  · exact hg g hm
  · exact hF g hm

end Qatlib.Concepts.CircuitImpl.MultiControl.CountFramedBorrowed
