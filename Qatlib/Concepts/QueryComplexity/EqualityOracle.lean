/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped Classical
namespace Qatlib.Concepts.QueryComplexity.EqualityOracle
variable {A X L : Type*} [Fintype A] [Fintype X]

abbrev Basis (A X : Type*) := A × X × X × Bool

def basisMap (f : X → L) (v : Basis A X) : Basis A X :=
  (v.1,v.2.1,v.2.2.1,if f v.2.1=f v.2.2.1 then !v.2.2.2 else v.2.2.2)
omit [Fintype A] [Fintype X] in

theorem basisMap_involutive (f : X → L) : Function.Involutive (basisMap (A := A) f) := by
  intro v
  rcases v with ⟨a,x,y,b⟩
  by_cases h : f x=f y <;> simp [basisMap,h]

def basisEquiv (f : X → L) : Basis A X ≃ Basis A X :=
  Function.Involutive.toPerm (basisMap f) (basisMap_involutive f)

def query (f : X → L) : EuclideanSpace ℂ (Basis A X) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Basis A X) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (basisEquiv f)
omit [Fintype A] [Fintype X] in

theorem basisMap_relabel (f : X → L) (σ : Equiv.Perm L) :
    basisMap (A := A) (σ ∘ f)=basisMap f := by
  funext v
  simp only [basisMap,Function.comp_apply,σ.injective.eq_iff]

theorem query_relabel (f : X → L) (σ : Equiv.Perm L) :
    query (A := A) (σ ∘ f)=query f := by
  have he : basisEquiv (A := A) (σ ∘ f)=basisEquiv f := by
    apply Equiv.ext
    exact congrFun (basisMap_relabel f σ)
  unfold query
  rw [he]

theorem query_single (f : X → L) (v : Basis A X) :
    query f (EuclideanSpace.single v (1 : ℂ))=EuclideanSpace.single (basisMap f v) (1 : ℂ) :=
  EuclideanSpace.piLpCongrLeft_single _ _ _

def state (f : X → L)
    (gates : ℕ → EuclideanSpace ℂ (Basis A X) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Basis A X))
    (initial : EuclideanSpace ℂ (Basis A X)) : ℕ → EuclideanSpace ℂ (Basis A X)
  | 0 => gates 0 initial
  | t+1 => gates (t+1) (query f (state f gates initial t))

theorem state_relabel (f : X → L) (σ : Equiv.Perm L)
    (gates : ℕ → EuclideanSpace ℂ (Basis A X) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Basis A X))
    (initial : EuclideanSpace ℂ (Basis A X)) (t : ℕ) :
    state (σ ∘ f) gates initial t=state f gates initial t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [state,query_relabel,ih]

theorem state_norm (f : X → L)
    (gates : ℕ → EuclideanSpace ℂ (Basis A X) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Basis A X))
    (initial : EuclideanSpace ℂ (Basis A X)) (t : ℕ) :
    ‖state f gates initial t‖=‖initial‖ := by
  induction t with
  | zero => exact (gates 0).norm_map initial
  | succ t ih => simpa only [state,LinearIsometryEquiv.norm_map] using ih
end Qatlib.Concepts.QueryComplexity.EqualityOracle
