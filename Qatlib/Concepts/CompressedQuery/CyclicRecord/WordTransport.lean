/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CompressedQuery.CyclicRecord.JointCompression
import Qatlib.Concepts.CompressedQuery.CyclicRecord.AlgorithmWord
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Concepts.CompressedQuery.CyclicRecord
variable {W X P L : Type*} [Fintype W] [Fintype X] [Fintype P] [Fintype L] [Nonempty L]

def sourceGrouping : EuclideanSpace ℂ (Registers W X P × (X → L)) ≃ₗᵢ[ℂ]
    PiLp 2 (fun _f : X → L => EuclideanSpace ℂ (Registers W X P)) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    ({toFun := fun b => (⟨b.2,b.1⟩ : Σ _f : X → L,Registers W X P)
      invFun := fun b => (b.2,b.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl} : (Registers W X P × (X → L)) ≃ Σ _f : X → L,Registers W X P)).trans
    (LinearIsometryEquiv.piLpCurry ℂ 2 (fun _f : X → L => fun _η : Registers W X P => ℂ))
omit [Nonempty L] in

theorem sourceGrouping_apply (ψ : EuclideanSpace ℂ (Registers W X P × (X → L)))
    (f : X → L) (η : Registers W X P) : sourceGrouping ψ f η=ψ (η,f) := rfl

def sourceGate (U : EuclideanSpace ℂ (Registers W X P) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Registers W X P)) :
    EuclideanSpace ℂ (Registers W X P × (X → L)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Registers W X P × (X → L)) :=
  (sourceGrouping.trans (LinearIsometryEquiv.piLpCongrRight 2 (fun _f : X → L => U))).trans sourceGrouping.symm
omit [Nonempty L] in

theorem sourceGate_apply
    (U : EuclideanSpace ℂ (Registers W X P) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Registers W X P))
    (ψ : EuclideanSpace ℂ (Registers W X P × (X → L))) (η : Registers W X P) (f : X → L) :
    sourceGate U ψ (η,f)=U (sourceGrouping ψ f) η := rfl

theorem compression_grouped (ψ : EuclideanSpace ℂ (Registers W X P × (X → L))) (db : X → Option L) :
    algorithmGrouping (jointCompressionAction ψ) db=
      ∑ f : X → L,tableCompression db f • sourceGrouping ψ f := by
  ext η
  change jointCompressionAction ψ (η,db)=_
  rw [jointCompressionAction_apply]
  simp
  rfl

theorem algorithmGate_compression
    (U : EuclideanSpace ℂ (Registers W X P) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Registers W X P))
    (ψ : EuclideanSpace ℂ (Registers W X P × (X → L))) :
    algorithmGate U (jointCompressionAction ψ)=jointCompressionAction (sourceGate U ψ) := by
  ext b
  rcases b with ⟨η,db⟩
  rw [algorithmGate_apply,compression_grouped,map_sum]
  simp_rw [map_smul]
  rw [jointCompressionAction_apply]
  simp [sourceGate_apply]

def sourceInitial (initial : EuclideanSpace ℂ (Registers W X P)) :
    EuclideanSpace ℂ (Registers W X P × (X → L)) :=
  WithLp.toLp 2 (fun b => (∏ _x : X,(coefficient L : ℂ))*initial b.1)

theorem compression_initial (initial : EuclideanSpace ℂ (Registers W X P)) :
    jointCompressionAction (sourceInitial initial)=initialDatabaseState (L := L) initial := by
  ext b
  rcases b with ⟨η,db⟩
  rw [jointCompressionAction_apply,initialDatabaseState_apply]
  change (∑ f : X → L,tableCompression db f*((∏ _x : X,(coefficient L : ℂ))*initial η))=_
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  have h := congrFun (tableCompression_uniform (X := X) (L := L)) db
  change (∑ f : X → L,tableCompression db f*(∏ _x : X,(coefficient L : ℂ)))=_ at h
  rw [h]
  by_cases he : db=(fun _ => none)
  · subst db
    simp
  · simp [he]

def sourceCheckpoint (phase : P → L → ℂ)
    (gates : ℕ → EuclideanSpace ℂ (Registers W X P) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Registers W X P))
    (initial : EuclideanSpace ℂ (Registers W X P)) : ℕ → EuclideanSpace ℂ (Registers W X P × (X → L))
  | 0 => sourceGate (gates 0) (sourceInitial initial)
  | t+1 => sourceGate (gates (t+1)) (standardPhase phase (sourceCheckpoint phase gates initial t))

theorem checkpoint_compression (phase : P → L → ℂ) (hp : ∀ p y,star (phase p y)*phase p y=1)
    (gates : ℕ → EuclideanSpace ℂ (Registers W X P) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Registers W X P))
    (initial : EuclideanSpace ℂ (Registers W X P)) (t : ℕ) :
    jointCompressionAction (sourceCheckpoint phase gates initial t)=checkpoint phase hp gates initial t := by
  induction t with
  | zero => rw [sourceCheckpoint,← algorithmGate_compression,compression_initial];rfl
  | succ t ih =>
    rw [sourceCheckpoint,← algorithmGate_compression,← databaseQuery_compression,ih]
    rfl
end Qatlib.Concepts.CompressedQuery.CyclicRecord
