/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.IsBotOne
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Disjoint
import Mathlib.Order.Heyting.Basic
import Mathlib.Order.Notation
import Mathlib.Order.RelClasses
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Möbius expansion of clause violation counts

Defines the subset-lattice transform `mobius` and proves its inversion formula. A function
depending on at most three variables has vanishing transform on subsets of size at least four.

Boolean literals and clause satisfaction define `unsatCount`. For clauses of size at most three,
`theorem2` reconstructs the violation count from its constant term and its Möbius coefficients
on subsets of sizes one, two, and three. See [VanDamMoscaVazirani2001].

## Main statements

* `mobius_inversion`: Recovers a set function by summing its subset coefficients.
* `mobius_eq_zero_of_local`: Local dependence on at most three variables forces higher
  coefficients to vanish.
* `theorem2`: Gives the degree-at-most-three expansion of a clause violation count.

## References

* [van Dam et al., 2001][VanDamMoscaVazirani2001]
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Finset

namespace Qatlib.Papers.AdiabPower02.MainResults
namespace Theorem2

variable {n : ℕ}

/-- The subset-lattice Möbius coefficient, the alternating sum of `F T` over subsets `T` of `S`. -/
def mobius (F : Finset (Fin n) → ℤ) (S : Finset (Fin n)) : ℤ :=
  ∑ T ∈ S.powerset, (-1 : ℤ) ^ (S.card - T.card) * F T

/-- The Möbius coefficient at the empty set equals the original function value there. -/
@[simp] lemma mobius_empty (F : Finset (Fin n) → ℤ) : mobius F ∅ = F ∅ := by
  simp [mobius]

/-- The Möbius transform preserves pointwise addition. -/
lemma mobius_add (F G : Finset (Fin n) → ℤ) (S : Finset (Fin n)) :
    mobius (fun I => F I + G I) S = mobius F S + mobius G S := by
  simp only [mobius, mul_add, Finset.sum_add_distrib]

/-- The Möbius transform commutes with finite sums of set functions. -/
lemma mobius_sum {ι : Type*} (s : Finset ι) (g : ι → Finset (Fin n) → ℤ)
    (S : Finset (Fin n)) :
    mobius (fun I => ∑ j ∈ s, g j I) S = ∑ j ∈ s, mobius (g j) S := by
  simp only [mobius]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.mul_sum]

/-- A nested sum over `R ⊆ S ⊆ J` can be reordered by first summing over `R`. -/
lemma sum_powerset_iterate_swap (J : Finset (Fin n))
    (h : Finset (Fin n) → Finset (Fin n) → ℤ) :
    (∑ S ∈ J.powerset, ∑ R ∈ S.powerset, h R S)
      = ∑ R ∈ J.powerset, ∑ S ∈ J.powerset.filter (fun S => R ⊆ S), h R S := by
  have inner : ∀ S ∈ J.powerset, (∑ R ∈ S.powerset, h R S)
      = ∑ R ∈ J.powerset, if R ⊆ S then h R S else 0 := by
    intro S hS
    have hS' : S ⊆ J := Finset.mem_powerset.mp hS
    have hset : S.powerset = J.powerset.filter (fun R => R ⊆ S) := by
      ext R
      simp only [Finset.mem_powerset, Finset.mem_filter]
      constructor
      · intro hRS; exact ⟨Finset.Subset.trans hRS hS', hRS⟩
      · intro h; exact h.2
    rw [hset, Finset.sum_filter]
  calc ∑ S ∈ J.powerset, ∑ R ∈ S.powerset, h R S
      = ∑ S ∈ J.powerset, ∑ R ∈ J.powerset, (if R ⊆ S then h R S else 0) :=
        Finset.sum_congr rfl inner
    _ = ∑ R ∈ J.powerset, ∑ S ∈ J.powerset, (if R ⊆ S then h R S else 0) :=
        Finset.sum_comm
    _ = ∑ R ∈ J.powerset, ∑ S ∈ J.powerset.filter (fun S => R ⊆ S), h R S := by
        refine Finset.sum_congr rfl fun R _ => ?_
        rw [Finset.sum_filter]

/-- For `R ⊆ J`, the alternating sum over supersets of `R` within `J` is one if `R = J` and zero
otherwise. -/
lemma sum_supersets_neg_one_pow (J R : Finset (Fin n)) (hR : R ⊆ J) :
    (∑ S ∈ J.powerset.filter (fun S => R ⊆ S), (-1 : ℤ) ^ (S.card - R.card))
      = if R = J then 1 else 0 := by
  have hset : J.powerset.filter (fun S => R ⊆ S)
      = (J \ R).powerset.image (fun U => R ∪ U) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
    constructor
    · rintro ⟨hSJ, hRS⟩
      refine ⟨S \ R, ?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_sdiff] at hx ⊢
        exact ⟨hSJ hx.1, hx.2⟩
      · ext x
        simp only [Finset.mem_union, Finset.mem_sdiff]
        constructor
        · rintro (h | ⟨h, _⟩)
          · exact hRS h
          · exact h
        · intro hx
          by_cases hxR : x ∈ R
          · exact Or.inl hxR
          · exact Or.inr ⟨hx, hxR⟩
    · rintro ⟨U, hU, rfl⟩
      refine ⟨?_, Finset.subset_union_left⟩
      intro x hx
      simp only [Finset.mem_union] at hx
      rcases hx with hx | hx
      · exact hR hx
      · exact (Finset.mem_sdiff.mp (hU hx)).1
  have hinj : ∀ U ∈ (J \ R).powerset, ∀ V ∈ (J \ R).powerset,
      R ∪ U = R ∪ V → U = V := by
    intro U hU V hV hUV
    have hUsub : U ⊆ J \ R := Finset.mem_powerset.mp hU
    have hVsub : V ⊆ J \ R := Finset.mem_powerset.mp hV
    have e1 : (R ∪ U) \ R = U := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hx | hx, hxR⟩
        · exact absurd hx hxR
        · exact hx
      · intro hx; exact ⟨Or.inr hx, (Finset.mem_sdiff.mp (hUsub hx)).2⟩
    have e2 : (R ∪ V) \ R = V := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hx | hx, hxR⟩
        · exact absurd hx hxR
        · exact hx
      · intro hx; exact ⟨Or.inr hx, (Finset.mem_sdiff.mp (hVsub hx)).2⟩
    rw [← e1, ← e2, hUV]
  rw [hset, Finset.sum_image hinj]
  have hcard : ∀ U ∈ (J \ R).powerset, (R ∪ U).card - R.card = U.card := by
    intro U hU
    have hUsub : U ⊆ J \ R := Finset.mem_powerset.mp hU
    have hdisj : Disjoint R U :=
      Finset.disjoint_of_subset_right hUsub Finset.disjoint_sdiff
    have hc : (R ∪ U).card = R.card + U.card := Finset.card_union_of_disjoint hdisj
    omega
  rw [Finset.sum_congr rfl (fun U hU => by rw [hcard U hU])]
  rw [Finset.sum_powerset_neg_one_pow_card]
  by_cases h : R = J
  · simp [h]
  · have hne : J \ R ≠ ∅ := by
      intro h0
      rw [Finset.sdiff_eq_empty_iff_subset] at h0
      exact h (Finset.Subset.antisymm hR h0)
    simp [h, hne]

/-- Every integer-valued set function equals the sum of its Möbius coefficients over subsets of
the input set. -/
theorem mobius_inversion (F : Finset (Fin n) → ℤ) (I : Finset (Fin n)) :
    F I = ∑ S ∈ I.powerset, mobius F S := by
  simp only [mobius]
  rw [sum_powerset_iterate_swap]
  rw [show (∑ T ∈ I.powerset, ∑ S ∈ I.powerset.filter (fun S => T ⊆ S),
        (-1 : ℤ) ^ (S.card - T.card) * F T)
      = ∑ T ∈ I.powerset, F T * ∑ S ∈ I.powerset.filter (fun S => T ⊆ S),
        (-1 : ℤ) ^ (S.card - T.card) from ?_]
  · rw [Finset.sum_congr rfl (fun T hT => by
        rw [sum_supersets_neg_one_pow I T (Finset.mem_powerset.mp hT)])]
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single I]
    · simp
    · intro T hT hTI
      simp [hTI]
    · intro hI; simp at hI
  · refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun S _ => by ring

/-- The subsets of cardinality between one and three form the union of the subsets of
cardinalities one, two, and three. -/
lemma powerset_low_card_split (I : Finset (Fin n)) :
    I.powerset.filter (fun S => 1 ≤ S.card ∧ S.card ≤ 3)
      = (I.powersetCard 1 ∪ I.powersetCard 2) ∪ I.powersetCard 3 := by
  ext S
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_union, Finset.mem_powersetCard]
  constructor
  · rintro ⟨hSI, h1, h3⟩
    rcases Nat.eq_or_lt_of_le h1 with h|h
    · left; left; exact ⟨hSI, h.symm⟩
    · rcases Nat.eq_or_lt_of_le h3 with h'|h'
      · right; exact ⟨hSI, by omega⟩
      · left; right; exact ⟨hSI, by omega⟩
  · rintro ((⟨hSI, h⟩ | ⟨hSI, h⟩) | ⟨hSI, h⟩)
    · exact ⟨hSI, by omega, by omega⟩
    · exact ⟨hSI, by omega, by omega⟩
    · exact ⟨hSI, by omega, by omega⟩

/-- If all Möbius coefficients on sets of size at least four vanish, the function is its
empty-set value plus its coefficient sums at sizes one, two, and three. -/
theorem mobius_truncation_card (F : Finset (Fin n) → ℤ)
    (hF : ∀ S, 4 ≤ S.card → mobius F S = 0) (I : Finset (Fin n)) :
    F I = F ∅
      + (∑ S ∈ I.powersetCard 1, mobius F S)
      + (∑ S ∈ I.powersetCard 2, mobius F S)
      + (∑ S ∈ I.powersetCard 3, mobius F S) := by

  have hdrop : F I = ∑ S ∈ I.powerset.filter (fun S => S.card ≤ 3), mobius F S := by
    rw [mobius_inversion F I]
    calc ∑ S ∈ I.powerset, mobius F S
        = ∑ S ∈ I.powerset, (if S.card ≤ 3 then mobius F S else 0) := by
          refine Finset.sum_congr rfl fun S _ => ?_
          by_cases hc : S.card ≤ 3
          · simp [hc]
          · have hle : 4 ≤ S.card := by omega
            simp [hc, hF S hle]
      _ = ∑ S ∈ I.powerset.filter (fun S => S.card ≤ 3), mobius F S := by
          rw [Finset.sum_filter]

  have hsplit : (∑ S ∈ I.powerset.filter (fun S => S.card ≤ 3), mobius F S)
      = F ∅ + ∑ S ∈ I.powerset.filter (fun S => 1 ≤ S.card ∧ S.card ≤ 3), mobius F S := by
    have hset : I.powerset.filter (fun S => S.card ≤ 3)
        = insert ∅ (I.powerset.filter (fun S => 1 ≤ S.card ∧ S.card ≤ 3)) := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert]
      constructor
      · rintro ⟨hSI, h3⟩
        rcases Nat.eq_or_lt_of_le (Nat.zero_le S.card) with h|h
        · left; exact Finset.card_eq_zero.mp h.symm
        · right; exact ⟨hSI, by omega, h3⟩
      · rintro (rfl | ⟨hSI, h1, h3⟩)
        · exact ⟨Finset.empty_subset I, by simp⟩
        · exact ⟨hSI, h3⟩
    have hnot : ∅ ∉ I.powerset.filter (fun S => 1 ≤ S.card ∧ S.card ≤ 3) := by
      simp
    rw [hset, Finset.sum_insert hnot, mobius_empty]

  have hunion : (∑ S ∈ I.powerset.filter (fun S => 1 ≤ S.card ∧ S.card ≤ 3), mobius F S)
      = (∑ S ∈ I.powersetCard 1, mobius F S)
        + (∑ S ∈ I.powersetCard 2, mobius F S)
        + (∑ S ∈ I.powersetCard 3, mobius F S) := by
    rw [powerset_low_card_split]
    have h12 : Disjoint (I.powersetCard 1) (I.powersetCard 2) := by
      rw [Finset.disjoint_left]
      intro S hS hS'
      simp only [Finset.mem_powersetCard] at hS hS'
      omega
    have h12' : Disjoint (I.powersetCard 1 ∪ I.powersetCard 2) (I.powersetCard 3) := by
      rw [Finset.disjoint_left]
      intro S hS hS'
      simp only [Finset.mem_union, Finset.mem_powersetCard] at hS hS'
      rcases hS with hS | hS <;> omega
    rw [Finset.sum_union h12', Finset.sum_union h12]
  rw [hdrop, hsplit, hunion]
  ring

/-- A Boolean literal represented by a variable index and a polarity bit. -/
abbrev Literal (n : ℕ) := Fin n × Bool

/-- The truth value of a literal when the set `I` records the variables assigned true. -/
def literalTrue (l : Literal n) (I : Finset (Fin n)) : Bool :=
  if l.2 then decide (l.1 ∈ I) else decide (l.1 ∉ I)

/-- The Boolean condition that at least one literal of a clause evaluates to true. -/
def clauseSat (c : Finset (Literal n)) (I : Finset (Fin n)) : Bool :=
  decide (∃ l ∈ c, literalTrue l I = true)

/-- The integer number of clauses in `Φ` that are unsatisfied by the assignment `I`. -/
def unsatCount (Φ : Finset (Finset (Literal n))) (I : Finset (Fin n)) : ℤ :=
  ∑ c ∈ Φ, (if clauseSat c I then (0 : ℤ) else 1)

/-- The finite set of variable indices occurring in a clause. -/
def clauseVars (c : Finset (Literal n)) : Finset (Fin n) := c.image Prod.fst

/-- The truth value of a literal in a clause is unchanged by restricting the assignment to that
clause's variables. -/
lemma literalTrue_inter_vars (c : Finset (Literal n)) (l : Literal n)
    (I : Finset (Fin n)) (hl : l ∈ c) :
    literalTrue l I = literalTrue l (I ∩ clauseVars c) := by
  have hv : l.1 ∈ clauseVars c := Finset.mem_image.mpr ⟨l, hl, rfl⟩
  have hiff : l.1 ∈ I ↔ l.1 ∈ I ∩ clauseVars c := by
    simp only [Finset.mem_inter]; exact ⟨fun h => ⟨h, hv⟩, fun h => h.1⟩
  unfold literalTrue
  by_cases hp : l.2
  · rw [if_pos hp, if_pos hp, decide_eq_decide]; exact hiff
  · rw [if_neg hp, if_neg hp, decide_eq_decide]; exact not_congr hiff

/-- Clause satisfaction is unchanged by restricting the assignment to the clause's variables. -/
lemma clauseSat_inter_vars (c : Finset (Literal n)) (I : Finset (Fin n)) :
    clauseSat c I = clauseSat c (I ∩ clauseVars c) := by
  unfold clauseSat
  rw [decide_eq_decide]
  constructor
  · rintro ⟨l, hl, ht⟩
    exact ⟨l, hl, by rw [← literalTrue_inter_vars c l I hl]; exact ht⟩
  · rintro ⟨l, hl, ht⟩
    exact ⟨l, hl, by rw [literalTrue_inter_vars c l I hl]; exact ht⟩

/-- Clause satisfaction is unchanged by restricting the assignment to any set containing all
variables of the clause. -/
lemma clauseSat_inter_of_subset (c : Finset (Literal n)) (T : Finset (Fin n))
    (hT : clauseVars c ⊆ T) (I : Finset (Fin n)) :
    clauseSat c I = clauseSat c (I ∩ T) := by
  rw [clauseSat_inter_vars c I, clauseSat_inter_vars c (I ∩ T)]
  have h : I ∩ clauseVars c = (I ∩ T) ∩ clauseVars c := by
    ext x
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨hxI, hxv⟩; exact ⟨⟨hxI, hT hxv⟩, hxv⟩
    · rintro ⟨⟨hxI, _⟩, hxv⟩; exact ⟨hxI, hxv⟩
  rw [h]

/-- The clause-unsatisfaction indicator depends only on the assignment restricted to the
clause's variables. -/
lemma clauseUnsat_local (c : Finset (Literal n)) :
    ∀ I, (if clauseSat c I then (0 : ℤ) else 1)
        = (if clauseSat c (I ∩ clauseVars c) then (0 : ℤ) else 1) := by
  intro I; rw [clauseSat_inter_vars]

/-- If a set function depends only on intersection with a set of at most three variables, its
Möbius coefficient vanishes on every set of size at least four. -/
lemma mobius_eq_zero_of_local (g : Finset (Fin n) → ℤ) (T : Finset (Fin n))
    (hT : T.card ≤ 3) (hg : ∀ I, g I = g (I ∩ T))
    (S : Finset (Fin n)) (hS : 4 ≤ S.card) : mobius g S = 0 := by
  obtain ⟨a, haS, haT⟩ : ∃ a ∈ S, a ∉ T := by
    by_contra h
    simp only [not_exists, not_and, Classical.not_not] at h
    have hST : S ⊆ T := fun x hx => h x hx
    have := Finset.card_le_card hST
    omega
  obtain ⟨S', hSeq, haS'⟩ : ∃ S', S = insert a S' ∧ a ∉ S' :=
    ⟨S.erase a, (Finset.insert_erase haS).symm, Finset.notMem_erase a S⟩
  subst hSeq
  rw [mobius]
  rw [Finset.sum_powerset_insert (s := S') (a := a) haS'
    (f := fun U => (-1 : ℤ) ^ ((insert a S').card - U.card) * g U)]
  have hcard : (insert a S').card = S'.card + 1 := Finset.card_insert_of_notMem haS'

  have hfirst : (∑ U ∈ S'.powerset, (-1 : ℤ) ^ ((insert a S').card - U.card) * g U)
      = -∑ U ∈ S'.powerset, (-1 : ℤ) ^ (S'.card - U.card) * g U := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun U hU => ?_
    have hUsub : U ⊆ S' := Finset.mem_powerset.mp hU
    have h1 : (insert a S').card - U.card = (S'.card - U.card) + 1 := by
      rw [hcard]; have := Finset.card_le_card hUsub; omega
    rw [h1, pow_succ]
    ring

  have hsecond : (∑ U ∈ S'.powerset,
        (-1 : ℤ) ^ ((insert a S').card - (insert a U).card) * g (insert a U))
      = ∑ U ∈ S'.powerset, (-1 : ℤ) ^ (S'.card - U.card) * g U := by
    refine Finset.sum_congr rfl fun U hU => ?_
    have hUsub : U ⊆ S' := Finset.mem_powerset.mp hU
    have haU : a ∉ U := fun h => haS' (hUsub h)
    have hcU : (insert a U).card = U.card + 1 := Finset.card_insert_of_notMem haU
    have h2 : (insert a S').card - (insert a U).card = S'.card - U.card := by
      rw [hcard, hcU]; have := Finset.card_le_card hUsub; omega
    have hgU : g (insert a U) = g U := by
      have hint : (insert a U) ∩ T = U ∩ T := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨hx | hx, hxT⟩
          · exact absurd (hx ▸ hxT) haT
          · exact ⟨hx, hxT⟩
        · rintro ⟨hx, hxT⟩; exact ⟨Or.inr hx, hxT⟩
      rw [hg (insert a U), hint, ← hg U]
    rw [h2, hgU]
  rw [hfirst, hsecond]
  ring

/-- The Möbius coefficient of the violation count is the sum of the coefficients of the
individual clause-unsatisfaction indicators. -/
lemma mobius_unsatCount (Φ : Finset (Finset (Literal n))) (S : Finset (Fin n)) :
    mobius (unsatCount Φ) S
      = ∑ c ∈ Φ, mobius (fun I => (if clauseSat c I then (0 : ℤ) else 1)) S := by
  unfold unsatCount
  exact mobius_sum Φ (fun c I => if clauseSat c I then (0 : ℤ) else 1) S

/-- For clauses of size at most three, every Möbius coefficient of the violation count on a set
of size at least four vanishes. -/
lemma mobius_unsatCount_eq_zero (Φ : Finset (Finset (Literal n)))
    (hΦ : ∀ c ∈ Φ, c.card ≤ 3) (S : Finset (Fin n)) (hS : 4 ≤ S.card) :
    mobius (unsatCount Φ) S = 0 := by
  rw [mobius_unsatCount]
  apply Finset.sum_eq_zero
  intro c hc
  refine mobius_eq_zero_of_local (fun I => (if clauseSat c I then (0 : ℤ) else 1))
    (clauseVars c) ?_ (clauseUnsat_local c) S hS
  calc (clauseVars c).card ≤ c.card := Finset.card_image_le
    _ ≤ 3 := hΦ c hc

/-- For a formula with clauses of size at most three, its violation count equals its
empty-assignment value plus its Möbius coefficient sums over subsets of sizes one, two, and
three [VanDamMoscaVazirani2001]. -/
theorem theorem2 (Φ : Finset (Finset (Literal n)))
    (hΦ : ∀ c ∈ Φ, c.card ≤ 3) (I : Finset (Fin n)) :
    unsatCount Φ I = unsatCount Φ ∅
      + (∑ S ∈ I.powersetCard 1, mobius (unsatCount Φ) S)
      + (∑ S ∈ I.powersetCard 2, mobius (unsatCount Φ) S)
      + (∑ S ∈ I.powersetCard 3, mobius (unsatCount Φ) S) :=
  mobius_truncation_card (unsatCount Φ) (mobius_unsatCount_eq_zero Φ hΦ) I

end Theorem2
end Qatlib.Papers.AdiabPower02.MainResults
