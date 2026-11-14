/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic
public import Mathlib.Tactic.FieldSimp.Lemmas

@[expose] public section

/-!
# Finite-group averaging and symmetry reduction

This module defines `groupAverage` for a finite group acting linearly on a real vector space.
Averaging produces a fixed point, preserves an invariant convex feasible set, and preserves an
invariant linear success functional; `symmetryReduction_successProbabilitySet` identifies the
attainable values with those attained on fixed points. See [Mochon2007] for the Hamiltonian
oracle formulation.

## Main statements

* `groupAverage_fixed`: The group average of x is fixed by every element of the acting group.
* `groupAverage_mem`: The average of a point in a convex set preserved by the group action
  remains in that set.
* `symmetryReduction_successProbabilitySet`: For a convex invariant feasible set and an
  invariant linear functional, the image of the feasible set equals the image of its group-fixed
  points.

## References

* [Mochon, 2007][Mochon2007]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HamOracle06.MainResults

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The cardinality of a finite group, regarded as a real number, is nonzero. -/
lemma card_cast_ne_zero (G : Type*) [Fintype G] [Group G] :
    (Fintype.card G : ℝ) ≠ 0 := by
  exact_mod_cast Fintype.card_ne_zero

/-- The normalized sum of the orbit of x under the finite-group linear action ρ. -/
def groupAverage (G : Type*) [Fintype G] [Group G]
    (ρ : G →* V ≃ₗ[ℝ] V) (x : V) : V :=
  (Fintype.card G : ℝ)⁻¹ • ∑ g : G, ρ g x

/-- The group average of x is fixed by every element of the acting group. -/
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

/-- The average of a point in a convex set preserved by the group action remains in that set. -/
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

/-- A linear functional invariant under the group action takes the same value on x and its group
average. -/
theorem groupAverage_successProbability (G : Type*) [Fintype G] [Group G]
    (ρ : G →* V ≃ₗ[ℝ] V) (f : V →ₗ[ℝ] ℝ)
    (hf : ∀ (g : G) (x : V), f (ρ g x) = f x) (x : V) :
    f (groupAverage G ρ x) = f x := by
  have hc : (Fintype.card G : ℝ) ≠ 0 := card_cast_ne_zero G
  unfold groupAverage
  rw [map_smul, map_sum, smul_eq_mul]
  simp only [hf, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- For a convex invariant feasible set and an invariant linear functional, the image of the
feasible set equals the image of its group-fixed points. See [Mochon2007]. -/
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
