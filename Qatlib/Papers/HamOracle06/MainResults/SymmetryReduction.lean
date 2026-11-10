/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Torsor.Defs
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp.Lemmas

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HamOracle06.MainResults

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

lemma card_cast_ne_zero (G : Type*) [Fintype G] [Group G] :
    (Fintype.card G : ℝ) ≠ 0 := by
  exact_mod_cast Fintype.card_ne_zero

def groupAverage (G : Type*) [Fintype G] [Group G]
    (ρ : G →* V ≃ₗ[ℝ] V) (x : V) : V :=
  (Fintype.card G : ℝ)⁻¹ • ∑ g : G, ρ g x

theorem groupAverage_fixed (G : Type*) [Fintype G] [Group G]
    (ρ : G →* V ≃ₗ[ℝ] V) (x : V) :
    ∀ g : G, ρ g (groupAverage G ρ x) = groupAverage G ρ x := by
  intro g
  unfold groupAverage
  rw [map_smul, map_sum]
  congr 1
  calc
    (∑ h : G, ρ g (ρ h x)) = ∑ h : G, ρ (g * h) x := by
      apply Finset.sum_congr rfl
      intro h _
      simp
    _ = ∑ h : G, ρ h x := by
      exact Fintype.sum_equiv (Equiv.mulLeft g) (fun h : G => ρ (g * h) x)
        (fun h : G => ρ h x) (fun h => rfl)

theorem groupAverage_mem (G : Type*) [Fintype G] [Group G]
    (ρ : G →* V ≃ₗ[ℝ] V) (S : Set V) (hconv : Convex ℝ S)
    (hS : ∀ g : G, Set.MapsTo (ρ g) S S) {x : V} (hx : x ∈ S) :
    groupAverage G ρ x ∈ S := by
  have hc : (Fintype.card G : ℝ) ≠ 0 := card_cast_ne_zero G
  have hw0 : ∀ g ∈ (Finset.univ : Finset G), (0 : ℝ) ≤ (Fintype.card G : ℝ)⁻¹ := by
    intro g _
    positivity
  have hw1 : ∑ g ∈ (Finset.univ : Finset G), (Fintype.card G : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have hz : ∀ g ∈ (Finset.univ : Finset G), ρ g x ∈ S := by
    intro g _
    exact hS g hx
  have h := hconv.sum_mem hw0 hw1 hz
  simpa [groupAverage, Finset.smul_sum] using h

theorem groupAverage_successProbability (G : Type*) [Fintype G] [Group G]
    (ρ : G →* V ≃ₗ[ℝ] V) (f : V →ₗ[ℝ] ℝ)
    (hf : ∀ (g : G) (x : V), f (ρ g x) = f x) (x : V) :
    f (groupAverage G ρ x) = f x := by
  have hc : (Fintype.card G : ℝ) ≠ 0 := card_cast_ne_zero G
  unfold groupAverage
  rw [map_smul, map_sum, smul_eq_mul]
  simp only [hf, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

theorem symmetryReduction_successProbabilitySet
    (G : Type*) [Fintype G] [Group G]
    (ρ : G →* V ≃ₗ[ℝ] V)
    (S : Set V) (hconv : Convex ℝ S)
    (hS : ∀ g : G, Set.MapsTo (ρ g) S S)
    (f : V →ₗ[ℝ] ℝ) (hf : ∀ (g : G) (x : V), f (ρ g x) = f x) :
    f '' S = f '' (S ∩ {x : V | ∀ g : G, ρ g x = x}) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    exact ⟨groupAverage G ρ x,
      ⟨groupAverage_mem G ρ S hconv hS hx, groupAverage_fixed G ρ x⟩,
      groupAverage_successProbability G ρ f hf x⟩
  · rintro y ⟨x, ⟨hxS, _⟩, rfl⟩
    exact ⟨x, hxS, rfl⟩

end Qatlib.Papers.HamOracle06.MainResults
