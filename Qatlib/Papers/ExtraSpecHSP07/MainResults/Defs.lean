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

set_option autoImplicit false

namespace Qatlib.Papers.ExtraSpecHSP07.MainResults

open scoped commutatorElement BigOperators

structure IsExtraspecial (G : Type*) [Group G] [Finite G] (p : ℕ) : Prop where

  prime : p.Prime

  commutator_eq_center : commutator G = Subgroup.center G

  center_eq_frattini : Subgroup.center G = frattini G

  center_card : Nat.card (Subgroup.center G) = p

theorem IsExtraspecial.commutator_card {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hE : IsExtraspecial G p) : Nat.card (commutator G) = p := by
  rw [hE.commutator_eq_center, hE.center_card]

def IsHidingFamily {G : Type*} [Group G] (H : Subgroup G) {σ : Type*} (ψ : G → σ) : Prop :=
  ∀ g g' : G, ψ g = ψ g' ↔ g⁻¹ * g' ∈ H

theorem IsHidingFamily.eq_of_mem {G : Type*} [Group G] {H : Subgroup G} {σ : Type*}
    {ψ : G → σ} (hψ : IsHidingFamily H ψ) {g g' : G} (h : g⁻¹ * g' ∈ H) : ψ g = ψ g' :=
  (hψ g g').mpr h

theorem IsHidingFamily.ne_of_not_mem {G : Type*} [Group G] {H : Subgroup G} {σ : Type*}
    {ψ : G → σ} (hψ : IsHidingFamily H ψ) {g g' : G} (h : g⁻¹ * g' ∉ H) : ψ g ≠ ψ g' :=
  fun hEq => h ((hψ g g').mp hEq)

theorem IsHidingFamily.mem_iff {G : Type*} [Group G] {H : Subgroup G} {σ : Type*}
    {ψ : G → σ} (hψ : IsHidingFamily H ψ) (g : G) : ψ g = ψ 1 ↔ g ∈ H := by
  simpa using hψ g 1

abbrev Abelianization (G : Type*) [Group G] : Type _ := G ⧸ commutator G

def abelianizationMap (G : Type*) [Group G] : G →* Abelianization G :=
  QuotientGroup.mk' (commutator G)

theorem comap_map_abelianizationMap (G : Type*) [Group G] (H : Subgroup G) :
    (Subgroup.map (abelianizationMap G) H).comap (abelianizationMap G) = H ⊔ commutator G := by
  rw [abelianizationMap, Subgroup.comap_map_eq, QuotientGroup.ker_mk']

def IsWitness (p : ℕ) (u : Fin 4 → ZMod p) (j : Fin 4 → (ZMod p)ˣ) : Prop :=
  (∑ i, u i * ((j i : ZMod p) - (j i : ZMod p) ^ 2) = 0) ∧
    (∑ i, u i * (j i : ZMod p) ^ 2 = 0)

def IsGoodVector (p : ℕ) (u : Fin 4 → ZMod p) : Prop :=
  ∃ j : Fin 4 → (ZMod p)ˣ, IsWitness p u j

structure HSPInterface.{u, v} (G : Type u) [Group G] [Finite G] where

  Solver : Subgroup G → Prop

  HidingProc : Subgroup G → Prop

  CreatesState : (σ : Type v) → σ → Prop

end Qatlib.Papers.ExtraSpecHSP07.MainResults
