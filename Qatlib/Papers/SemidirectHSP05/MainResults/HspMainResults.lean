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

/-!
# Hidden subgroup interfaces and semidirect product identities

This module defines `HidesSubgroup`, legacy output specifications, and an unproved
query-bound statement requiring an adaptive query-tree implementation. This deterministic
query model does not construct the paper's quantum algorithm or bound classical runtime.
The proved results are algebraic ingredients associated with Lemma 1 and Theorem 4 of
[BaconChildsVanDam2005]: the prime-order quotient dichotomy, containment in the abelian factor,
and finite geometric sum identities.

## Main statements

* `lemma1_subgroup_dichotomy`: The projection of a subgroup onto the prime-order factor is
  trivial or surjective.
* `lemma1_le_range_inl_of_map_eq_bot`: A subgroup with trivial projection lies in the left
  factor.
* `theorem4_geom_sum_zmod`: A nontrivial geometric sum with p terms over ZMod p equals one.

## References

* [Bacon et al., 2005][BaconChildsVanDam2005]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemidirectHSP05.MainResults.HspMainResults

/-- A function hides a subgroup when two inputs have equal values exactly when they belong to
the same left coset of that subgroup. -/
def HidesSubgroup {G : Type*} [Group G] (f : G → ℕ) (H : Subgroup G) : Prop :=
  ∀ x y : G, f x = f y ↔ x⁻¹ * y ∈ H

/-- Legacy output specification with a query label. Alone it has no oracle-access
semantics; `HspProcedure.Implemented` supplies those semantics. -/
structure HspProcedure (G : Type*) [Group G] where

  queries : ℕ

  solve : (G → ℕ) → Finset G

namespace HspProcedure

variable {G : Type*} [Group G]

/-- Output correctness only: no query bound or implementation is certified. -/
def Solves (P : Subgroup G → Prop) (proc : HspProcedure G) : Prop :=
  ∀ (f : G → ℕ) (H : Subgroup G), P H → HidesSubgroup f H →
    Subgroup.closure (proc.solve f : Set G) = H

/-- A depth-indexed deterministic adaptive oracle tree. Each `query` node makes
one call at its fixed group element and branches only on the returned value.
The leaf output cannot inspect the oracle. -/
inductive QueryTree (G : Type*) : ℕ → Type _ where
  | result (output : Finset G) : QueryTree G 0
  | query {k : ℕ} (input : G) (next : ℕ → QueryTree G k) : QueryTree G (k + 1)

/-- Execute the query tree, with exactly its indexed number of oracle calls. -/
def QueryTree.run {k : ℕ} : QueryTree G k → (G → ℕ) → Finset G
  | .result output, _ => output
  | .query input next, f => (next (f input)).run f

/-- The stored query count is the depth of a tree computing the stored output.
This models deterministic queries with unrestricted classical postprocessing. -/
def Implemented (proc : HspProcedure G) : Prop :=
  ∃ tree : QueryTree G proc.queries, ∀ f, proc.solve f = tree.run f

end HspProcedure

/-- **Statement only — not proved in Qatlib.** Existence of a deterministic
query-tree implementation solving the promise with the displayed query bound.
This is not a formalization of quantum query access or of efficient classical computation.
The bound is for the supplied `size`, with no uniformity assertion across sizes. -/
def efficientPromisedHsp_statement (G : Type*) [Group G]
    (P : Subgroup G → Prop) (size : ℕ) : Prop :=
  ∃ c : ℕ, ∃ proc : HspProcedure G,
    proc.Implemented ∧ proc.Solves P ∧ proc.queries ≤ c * (Nat.log2 size + 1) ^ c

/-- **Statement only — not proved in Qatlib.** Compatibility name for
`efficientPromisedHsp_statement`; now requires an actual query-tree implementation. -/
def EfficientPromisedHsp (G : Type*) [Group G] (P : Subgroup G → Prop) (size : ℕ) : Prop :=
  efficientPromisedHsp_statement G P size

section Lemma1

variable {A : Type*} [AddCommGroup A]

/-- The subgroup is trivial or is generated by an element `(d, 1)` with `d` in `A₂` and has
cardinality `p`. -/
def cyclicOrderPPromise (p : ℕ) (A₂ : AddSubgroup A)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative A)) :
    Subgroup (SemidirectProduct (Multiplicative A) (Multiplicative (ZMod p)) φ) → Prop :=
  fun H => H = ⊥ ∨ ∃ d : A, d ∈ A₂ ∧
    H = Subgroup.closure
      {SemidirectProduct.mk (Multiplicative.ofAdd d) (1 : Multiplicative (ZMod p))} ∧
    Nat.card H = p

/-- For prime `p`, the image of a subgroup of the semidirect product under the projection to
`Multiplicative (ZMod p)` is either trivial or the whole group. This is an algebraic
ingredient of Lemma 1 of [BaconChildsVanDam2005]. -/
theorem lemma1_subgroup_dichotomy (p : ℕ) (hp : p.Prime)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative A))
    (H : Subgroup (SemidirectProduct (Multiplicative A) (Multiplicative (ZMod p)) φ)) :
    H.map (SemidirectProduct.rightHom (φ := φ)) = ⊥ ∨
      H.map (SemidirectProduct.rightHom (φ := φ)) = ⊤ := by
  have hcard : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_congr (Multiplicative.toAdd (α := ZMod p)), Nat.card_zmod]
  haveI : Fact (Nat.card (Multiplicative (ZMod p))).Prime := ⟨by rw [hcard]; exact hp⟩
  exact Subgroup.eq_bot_or_eq_top_of_prime_card _

/-- A subgroup with trivial image under the right projection is contained in the image of the
left inclusion, as used in Lemma 1 of [BaconChildsVanDam2005]. -/
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

/-- The kth power of `(d, 1)` in the semidirect product is `(k • d, 1)` [BaconChildsVanDam2005]. -/
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

/-- The subgroup generated by `(d, 1)` is contained in the image of the left inclusion
[BaconChildsVanDam2005]. -/
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

/-- Multiplying the finite geometric sum of powers of `u` by `u - 1` gives `u ^ b - 1` in a
commutative ring. This identity is used in the setting of Theorem 4 of
[BaconChildsVanDam2005]. -/
theorem theorem4_geometric_sum {R : Type*} [CommRing R] (u : R) (b : ℕ) :
    (u - 1) * ∑ j ∈ Finset.range b, u ^ j = u ^ b - 1 :=
  mul_geom_sum u b

/-- For prime `p` and `u ≠ 1` in `ZMod p`, the sum of `u ^ j` for `0 ≤ j < p` equals one
[BaconChildsVanDam2005]. -/
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
