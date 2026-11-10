/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionLB26.QueryModel.ActualWord
import Qatlib.Concepts.AdversaryBounds.LabelProgress.RelabelGram
import Qatlib.Concepts.AdversaryBounds.LabelProgress.SupportRange
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
open Matrix Module
open scoped Classical BigOperators
namespace Qatlib.Papers.CollisionLB26.SpaceOrbit
open Qatlib.Papers.CollisionLB26.QueryDefs
open Qatlib.Concepts.AdversaryBounds.LabelProgress
variable {W : Type*} [Fintype W] {M N : ℕ} [NeZero N]
local instance : DecidableEq (Fin M) := fun a b => Classical.propDecidable (a=b)

def recordRelabel (σ : Equiv.Perm (ZMod N)) : Equiv.Perm (Fin M → Option (ZMod N)) where
  toFun db x := Option.map σ (db x)
  invFun db x := Option.map σ.symm (db x)
  left_inv db := by
    funext x
    change Option.map σ.symm (Option.map σ (db x))=db x
    cases db x <;> simp
  right_inv db := by
    funext x
    change Option.map σ (Option.map σ.symm (db x))=db x
    cases db x <;> simp
omit [NeZero N] in

theorem recordRelabel_mul (σ τ : Equiv.Perm (ZMod N)) :
    recordRelabel (M := M) (σ*τ)=recordRelabel σ*recordRelabel τ := by
  apply Equiv.ext
  intro db
  funext x
  change Option.map (σ*τ) (db x)=Option.map σ (Option.map τ (db x))
  cases db x <;> rfl

def jointCoefficients
    (gates : ℕ → EuclideanSpace ℂ (AlgorithmRegisters W M N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (AlgorithmRegisters W M N))
    (initial : EuclideanSpace ℂ (AlgorithmRegisters W M N)) (t : ℕ) :
    Matrix (Fin M → Option (ZMod N)) (AlgorithmRegisters W M N) ℂ :=
  fun db η => actualCheckpoint gates initial t (η,db)

def LabelSymmetricAt
    (gates : ℕ → EuclideanSpace ℂ (AlgorithmRegisters W M N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (AlgorithmRegisters W M N))
    (initial : EuclideanSpace ℂ (AlgorithmRegisters W M N)) (t : ℕ) : Prop :=
  ∀ σ : Equiv.Perm (ZMod N),
    (reducedInput (jointCoefficients gates initial t)).mulVecLin.comp (inputRelabel (recordRelabel σ)).toLinearMap=
      (inputRelabel (recordRelabel σ)).toLinearMap.comp (reducedInput (jointCoefficients gates initial t)).mulVecLin

theorem actual_reduced_rank
    (gates : ℕ → EuclideanSpace ℂ (AlgorithmRegisters W M N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (AlgorithmRegisters W M N))
    (initial : EuclideanSpace ℂ (AlgorithmRegisters W M N)) (t : ℕ) :
    (reducedInput (jointCoefficients gates initial t)).rank ≤ Fintype.card W*M*N := by
  rw [← actual_algorithm_dimension (W := W) (M := M) (N := N)]
  exact reducedInput_rank (jointCoefficients gates initial t)

theorem actual_orbit_bound
    (gates : ℕ → EuclideanSpace ℂ (AlgorithmRegisters W M N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (AlgorithmRegisters W M N))
    (initial : EuclideanSpace ℂ (AlgorithmRegisters W M N)) (t S : ℕ)
    (hsym : LabelSymmetricAt gates initial t) (hspace : Fintype.card (AlgorithmRegisters W M N) ≤ 2^S)
    (v : (Fin M → Option (ZMod N)) → ℂ) (hv : v ∈ support (jointCoefficients gates initial t)) :
    finrank ℂ (orbitSpan (fun σ : Equiv.Perm (ZMod N) => inputRelabel (recordRelabel σ)) v) ≤ 2^S :=
  actual_qubit_orbit (jointCoefficients gates initial t) _ hsym S hspace v hv

theorem actual_component_mem_support
    (gates : ℕ → EuclideanSpace ℂ (AlgorithmRegisters W M N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (AlgorithmRegisters W M N))
    (initial : EuclideanSpace ℂ (AlgorithmRegisters W M N)) (t : ℕ) (η : AlgorithmRegisters W M N) :
    (fun db => actualCheckpoint gates initial t (η,db)) ∈ support (jointCoefficients gates initial t) :=
  amplitude_column_mem_support (jointCoefficients gates initial t) η

theorem actual_component_orbit
    (gates : ℕ → EuclideanSpace ℂ (AlgorithmRegisters W M N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (AlgorithmRegisters W M N))
    (initial : EuclideanSpace ℂ (AlgorithmRegisters W M N)) (t S : ℕ)
    (hsym : LabelSymmetricAt gates initial t) (hspace : Fintype.card (AlgorithmRegisters W M N) ≤ 2^S)
    (η : AlgorithmRegisters W M N) :
    finrank ℂ (orbitSpan (fun σ : Equiv.Perm (ZMod N) => inputRelabel (recordRelabel σ))
      (fun db => actualCheckpoint gates initial t (η,db))) ≤ 2^S :=
  actual_orbit_bound gates initial t S hsym hspace _ (actual_component_mem_support gates initial t η)
end Qatlib.Papers.CollisionLB26.SpaceOrbit
