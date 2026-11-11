/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Equality queries invariant under label permutations

This module defines an equality oracle that compares the labels of two query positions and
toggles an answer bit when they agree. The involutive basis map induces the linear isometry
`query`, and `state` alternates this query with arbitrary specified isometric gates.

The basis map, query, and complete evolution are invariant under permutations of the label
space, and the evolution preserves the initial norm. The construction specializes the standard
quantum query-circuit framework [NielsenChuang2010] to equality comparisons.

## Main statements

* `basisMap_involutive`: the basis action is an involution.
* `query_relabel`: label permutations preserve the query operator.
* `state_relabel`: label permutations preserve every evolved state.
* `state_norm`: query evolution preserves the initial norm.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option autoImplicit false
noncomputable section
open scoped Classical
namespace Qatlib.Concepts.QueryComplexity.EqualityOracle
variable {A X L : Type*} [Fintype A] [Fintype X]

/-- The basis index for an auxiliary register, two query positions, and a Boolean answer bit. -/
abbrev Basis (A X : Type*) := A × X × X × Bool

/-- Toggles the answer bit exactly when the two queried positions have equal labels under `f`. -/
def basisMap (f : X → L) (v : Basis A X) : Basis A X :=
  (v.1,v.2.1,v.2.2.1,if f v.2.1=f v.2.2.1 then !v.2.2.2 else v.2.2.2)
omit [Fintype A] [Fintype X] in

/-- The equality-oracle basis map is an involution. -/
theorem basisMap_involutive (f : X → L) : Function.Involutive (basisMap (A := A) f) := by
  intro v
  rcases v with ⟨a,x,y,b⟩
  by_cases h : f x=f y <;> simp [basisMap,h]

/-- The basis permutation determined by the involutive equality-oracle map. -/
def basisEquiv (f : X → L) : Basis A X ≃ Basis A X :=
  Function.Involutive.toPerm (basisMap f) (basisMap_involutive f)

/-- The complex linear isometry equivalence induced by the equality-oracle basis permutation. -/
def query (f : X → L) : EuclideanSpace ℂ (Basis A X) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Basis A X) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (basisEquiv f)
omit [Fintype A] [Fintype X] in

/-- Permuting the label space of `f` leaves the equality-oracle basis map unchanged. -/
theorem basisMap_relabel (f : X → L) (σ : Equiv.Perm L) :
    basisMap (A := A) (σ ∘ f)=basisMap f := by
  funext v
  simp only [basisMap,Function.comp_apply,σ.injective.eq_iff]

/-- Permuting the label space of `f` leaves the equality-query operator unchanged. -/
theorem query_relabel (f : X → L) (σ : Equiv.Perm L) :
    query (A := A) (σ ∘ f)=query f := by
  have he : basisEquiv (A := A) (σ ∘ f)=basisEquiv f := by
    apply Equiv.ext
    exact congrFun (basisMap_relabel f σ)
  unfold query
  rw [he]

/-- The equality query sends a unit basis vector to the basis vector indexed by its basis-map
image. -/
theorem query_single (f : X → L) (v : Basis A X) :
    query f (EuclideanSpace.single v (1 : ℂ))=EuclideanSpace.single (basisMap f v) (1 : ℂ) :=
  EuclideanSpace.piLpCongrLeft_single _ _ _

/-- The state after alternating equality queries with the specified isometric gates, starting
with gate zero on the initial state. -/
def state (f : X → L)
    (gates : ℕ → EuclideanSpace ℂ (Basis A X) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Basis A X))
    (initial : EuclideanSpace ℂ (Basis A X)) : ℕ → EuclideanSpace ℂ (Basis A X)
  | 0 => gates 0 initial
  | t+1 => gates (t+1) (query f (state f gates initial t))

/-- Every state in the equality-query evolution is unchanged by a permutation of the input
labels. -/
theorem state_relabel (f : X → L) (σ : Equiv.Perm L)
    (gates : ℕ → EuclideanSpace ℂ (Basis A X) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Basis A X))
    (initial : EuclideanSpace ℂ (Basis A X)) (t : ℕ) :
    state (σ ∘ f) gates initial t=state f gates initial t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [state,query_relabel,ih]

/-- Alternating equality queries and isometric gates preserves the norm of the initial state. -/
theorem state_norm (f : X → L)
    (gates : ℕ → EuclideanSpace ℂ (Basis A X) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Basis A X))
    (initial : EuclideanSpace ℂ (Basis A X)) (t : ℕ) :
    ‖state f gates initial t‖=‖initial‖ := by
  induction t with
  | zero => exact (gates 0).norm_map initial
  | succ t ih => simpa only [state,LinearIsometryEquiv.norm_map] using ih
end Qatlib.Concepts.QueryComplexity.EqualityOracle
