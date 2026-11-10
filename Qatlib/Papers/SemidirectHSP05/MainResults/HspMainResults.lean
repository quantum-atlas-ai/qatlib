/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.Nat
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.Logic.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Mathlib.Data.ZMod.Defs
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import Mathlib.Logic.Equiv.Defs
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Notation
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemidirectHSP05.MainResults.HspMainResults

def HidesSubgroup {G : Type*} [Group G] (f : G → ℕ) (H : Subgroup G) : Prop :=
  ∀ x y : G, f x = f y ↔ x⁻¹ * y ∈ H

structure HspProcedure (G : Type*) [Group G] where

  queries : ℕ

  solve : (G → ℕ) → Finset G

namespace HspProcedure

variable {G : Type*} [Group G]

def Solves (P : Subgroup G → Prop) (proc : HspProcedure G) : Prop :=
  ∀ (f : G → ℕ) (H : Subgroup G), P H → HidesSubgroup f H →
    Subgroup.closure (proc.solve f : Set G) = H

end HspProcedure

def EfficientPromisedHsp (G : Type*) [Group G] (P : Subgroup G → Prop) (size : ℕ) : Prop :=
  ∃ c : ℕ, ∃ proc : HspProcedure G,
    proc.Solves P ∧ proc.queries ≤ c * (Nat.log2 size + 1) ^ c

section Lemma1

variable {A : Type*} [AddCommGroup A]

def cyclicOrderPPromise (p : ℕ) (A₂ : AddSubgroup A)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative A)) :
    Subgroup (SemidirectProduct (Multiplicative A) (Multiplicative (ZMod p)) φ) → Prop :=
  fun H => H = ⊥ ∨ ∃ d : A, d ∈ A₂ ∧
    H = Subgroup.closure
      {SemidirectProduct.mk (Multiplicative.ofAdd d) (1 : Multiplicative (ZMod p))} ∧
    Nat.card H = p

theorem lemma1_subgroup_dichotomy (p : ℕ) (hp : p.Prime)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative A))
    (H : Subgroup (SemidirectProduct (Multiplicative A) (Multiplicative (ZMod p)) φ)) :
    H.map (SemidirectProduct.rightHom (φ := φ)) = ⊥ ∨
      H.map (SemidirectProduct.rightHom (φ := φ)) = ⊤ := by
  have hcard : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_congr (Multiplicative.toAdd (α := ZMod p)), Nat.card_zmod]
  haveI : Fact (Nat.card (Multiplicative (ZMod p))).Prime := ⟨by rw [hcard]; exact hp⟩
  exact Subgroup.eq_bot_or_eq_top_of_prime_card _

theorem lemma1_le_range_inl_of_map_eq_bot (p : ℕ)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative A))
    (H : Subgroup (SemidirectProduct (Multiplicative A) (Multiplicative (ZMod p)) φ))
    (h : H.map (SemidirectProduct.rightHom (φ := φ)) = ⊥) :
    H ≤ (SemidirectProduct.inl (φ := φ)).range := by
  intro x hx
  rw [SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
  have hx' : SemidirectProduct.rightHom x ∈ H.map (SemidirectProduct.rightHom (φ := φ)) :=
    ⟨x, hx, rfl⟩
  rw [h] at hx'
  simpa using hx'

theorem mk_one_pow (p : ℕ)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative A)) (d : A) (k : ℕ) :
    (SemidirectProduct.mk (Multiplicative.ofAdd d) (1 : Multiplicative (ZMod p)) :
        SemidirectProduct (Multiplicative A) (Multiplicative (ZMod p)) φ) ^ k =
      SemidirectProduct.mk (Multiplicative.ofAdd (k • d))
        (1 : Multiplicative (ZMod p)) := by
  induction k with
  | zero => ext <;> simp
  | succ k ih =>
      rw [pow_succ, ih, SemidirectProduct.mul_def]
      ext <;> simp [succ_nsmul]

theorem lemma1_promise_cyclic_in_A (p : ℕ)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative A)) (d : A) :
    Subgroup.closure
        {SemidirectProduct.mk (Multiplicative.ofAdd d) (1 : Multiplicative (ZMod p))} ≤
      (SemidirectProduct.inl (φ := φ)).range := by
  rw [SemidirectProduct.range_inl_eq_ker_rightHom, Subgroup.closure_le]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  simp only [SetLike.mem_coe, MonoidHom.mem_ker]
  simp [SemidirectProduct.rightHom]

end Lemma1

section Theorem4

theorem theorem4_geometric_sum {R : Type*} [CommRing R] (u : R) (b : ℕ) :
    (u - 1) * ∑ j ∈ Finset.range b, u ^ j = u ^ b - 1 :=
  mul_geom_sum u b

theorem theorem4_geom_sum_zmod (p : ℕ) [Fact p.Prime] (u : ZMod p) (hu : u ≠ 1) :
    ∑ j ∈ Finset.range p, u ^ j = 1 := by
  have h := mul_geom_sum u p
  rw [ZMod.pow_card] at h
  have hne : u - 1 ≠ 0 := sub_ne_zero.mpr hu
  have h' : (u - 1) * (∑ j ∈ Finset.range p, u ^ j) = (u - 1) * 1 := by
    rw [h]; ring
  exact mul_left_cancel₀ hne h'

end Theorem4

end Qatlib.Papers.SemidirectHSP05.MainResults.HspMainResults
