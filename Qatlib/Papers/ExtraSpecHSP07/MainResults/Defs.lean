/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.Coset.Card

/-!
# Extraspecial groups and hidden subgroup interfaces

This module records the group-theoretic properties used for extraspecial groups, hiding
families, and passage to the quotient by the commutator subgroup. It also defines
four-coordinate witness equations and an abstract `HSPInterface` containing predicates for
solving, hiding, and state creation. These statements formalize components of
[IvanyosSanselmeSantha2007].

## Main statements

* `comap_map_abelianizationMap`: recovers `H ⊔ commutator G` by mapping and pulling back through
  the quotient.
* `IsWitness`: states the two equations for a unit-valued witness vector.
* `HSPInterface`: specifies abstract predicates for the hidden subgroup development.

## References

* [Ivanyos et al., 2007][IvanyosSanselmeSantha2007]
-/

set_option autoImplicit false

namespace Qatlib.Papers.ExtraSpecHSP07.MainResults

open scoped commutatorElement BigOperators

/-- The finite group has coincident commutator, center, and Frattini subgroups, with the center
of prime cardinality `p`. -/
structure IsExtraspecial (G : Type*) [Group G] [Finite G] (p : ℕ) : Prop where

  prime : p.Prime

  commutator_eq_center : commutator G = Subgroup.center G

  center_eq_frattini : Subgroup.center G = frattini G

  center_card : Nat.card (Subgroup.center G) = p

/-- In a group satisfying `IsExtraspecial G p`, the commutator subgroup has cardinality `p`. -/
theorem IsExtraspecial.commutator_card {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hE : IsExtraspecial G p) : Nat.card (commutator G) = p := by
  rw [hE.commutator_eq_center, hE.center_card]

/-- The family `ψ` takes equal values precisely on pairs whose relative element `g⁻¹ * g'`
belongs to `H`. -/
def IsHidingFamily {G : Type*} [Group G] (H : Subgroup G) {σ : Type*} (ψ : G → σ) : Prop :=
  ∀ g g' : G, ψ g = ψ g' ↔ g⁻¹ * g' ∈ H

/-- A hiding family takes equal values when the relative group element lies in the hidden
subgroup. -/
theorem IsHidingFamily.eq_of_mem {G : Type*} [Group G] {H : Subgroup G} {σ : Type*}
    {ψ : G → σ} (hψ : IsHidingFamily H ψ) {g g' : G} (h : g⁻¹ * g' ∈ H) : ψ g = ψ g' :=
  (hψ g g').mpr h

/-- A hiding family takes distinct values when the relative group element lies outside the
hidden subgroup. -/
theorem IsHidingFamily.ne_of_not_mem {G : Type*} [Group G] {H : Subgroup G} {σ : Type*}
    {ψ : G → σ} (hψ : IsHidingFamily H ψ) {g g' : G} (h : g⁻¹ * g' ∉ H) : ψ g ≠ ψ g' :=
  fun hEq => h ((hψ g g').mp hEq)

/-- For a family hiding `H`, equality of the values at `g` and the identity is equivalent to `g
∈ H`. -/
theorem IsHidingFamily.mem_iff {G : Type*} [Group G] {H : Subgroup G} {σ : Type*}
    {ψ : G → σ} (hψ : IsHidingFamily H ψ) (g : G) : ψ g = ψ 1 ↔ g ∈ H := by
  simpa using hψ g 1

/-- The quotient of `G` by its commutator subgroup. -/
abbrev Abelianization (G : Type*) [Group G] : Type _ := G ⧸ commutator G

/-- The canonical group homomorphism from `G` to its quotient by the commutator subgroup. -/
def abelianizationMap (G : Type*) [Group G] : G →* Abelianization G :=
  QuotientGroup.mk' (commutator G)

/-- Mapping `H` to the commutator quotient and pulling it back gives `H ⊔ commutator G`. -/
theorem comap_map_abelianizationMap (G : Type*) [Group G] (H : Subgroup G) :
    (Subgroup.map (abelianizationMap G) H).comap (abelianizationMap G) = H ⊔ commutator G := by
  rw [abelianizationMap, Subgroup.comap_map_eq, QuotientGroup.ker_mk']

/-- The unit-valued vector `j` satisfies `∑ i, u i * (j i - (j i) ^ 2) = 0` and `∑ i, u i * (j
i) ^ 2 = 0` in `ZMod p`. -/
def IsWitness (p : ℕ) (u : Fin 4 → ZMod p) (j : Fin 4 → (ZMod p)ˣ) : Prop :=
  (∑ i, u i * ((j i : ZMod p) - (j i : ZMod p) ^ 2) = 0) ∧
    (∑ i, u i * (j i : ZMod p) ^ 2 = 0)

/-- The vector `u` possesses a unit-valued four-coordinate witness satisfying `IsWitness p u`. -/
def IsGoodVector (p : ℕ) (u : Fin 4 → ZMod p) : Prop :=
  ∃ j : Fin 4 → (ZMod p)ˣ, IsWitness p u j

/-- An abstract interface specifying predicates for subgroup solvers, subgroup hiding
procedures, and creation of states of a supplied type. -/
structure HSPInterface.{u, v} (G : Type u) [Group G] [Finite G] where

  Solver : Subgroup G → Prop

  HidingProc : Subgroup G → Prop

  CreatesState : (σ : Type v) → σ → Prop

end Qatlib.Papers.ExtraSpecHSP07.MainResults
