/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Torsor.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Data.SetLike.Fintype
import Mathlib.GroupTheory.Index
import Mathlib.Logic.Equiv.Defs
import Mathlib.Order.Atoms
import Mathlib.Order.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Defs.Unbundled
import Mathlib.Order.Notation
import Mathlib.Order.Preorder.Finite
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Qatlib.Papers.NonabelianHSP98.MainResults.Lemma63.Basic
import Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup

/-!
# Generation bounds from maximal subgroups

This module counts tuples contained in maximal proper subgroups to bound the failure probability
of random generation. The estimate `genProb_ge_one_sub_maxSubs` depends explicitly on the number
of maximal subgroups. Its corrected corollaries give a bound for `4 * j` samples under the
hypotheses `card (maxSubs G) ≤ 2 ^ d` and `3 * d ≤ j`. This development accompanies
[RoettelerBeth1998].

## Main statements

* `card_fail_le`: a union bound for nongenerating tuples.
* `genProb_ge_one_sub_maxSubs`: a generation probability lower bound.
* `genProb_ge_corrected`: a corrected sample bound with explicit maximal-subgroup assumptions.

## References

* [Roetteler and Beth, 1998][RoettelerBeth1998]
-/

set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Qatlib.Papers.NonabelianHSP98.MainResults.Lemma63

open Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup
open Finset
open scoped BigOperators

variable {G : Type} [Fintype G] [Group G]

/-- The finite set of maximal proper subgroups of `G`. -/
noncomputable def maxSubs (G : Type) [Fintype G] [Group G] : Finset (Subgroup G) := by
  classical
  exact Finset.univ.filter (fun K : Subgroup G => IsCoatom K)

/-- The finite set of ordered `i`-tuples that generate `G`. -/
noncomputable def genSet (G : Type) [Fintype G] [Group G] (i : ℕ) : Finset (Fin i → G) := by
  classical
  exact Finset.univ.filter (fun S : Fin i → G => Subgroup.closure (Set.range S) = ⊤)

/-- The finite set of ordered `i`-tuples that fail to generate `G`. -/
noncomputable def failSet (G : Type) [Fintype G] [Group G] (i : ℕ) : Finset (Fin i → G) := by
  classical
  exact Finset.univ.filter (fun S : Fin i → G => Subgroup.closure (Set.range S) ≠ ⊤)

/-- A subgroup is a coatom in the subgroup lattice if and only if it is maximal among proper
subgroups. -/
theorem isCoatom_iff_maximal_lt_top (K : Subgroup G) :
    IsCoatom K ↔ Maximal (fun H : Subgroup G => H < ⊤) K := by
  constructor
  · intro h
    refine ⟨h.lt_top, ?_⟩
    intro c hc hKc
    by_contra hcK
    have hlt : K < c :=
      lt_of_le_of_ne hKc (fun hEq => hcK (le_of_eq hEq.symm))
    exact hc.ne (h.lt_iff.mp hlt)
  · rintro ⟨hlt, hmax⟩
    refine ⟨ne_of_lt hlt, ?_⟩
    intro b hKb
    by_contra hb
    have hblt : b < ⊤ := lt_top_iff_ne_top.mpr hb
    exact (not_lt_of_ge (hmax hblt hKb.le)) hKb

/-- Every proper subgroup of a finite group is contained in a maximal proper subgroup. -/
theorem exists_coatom_of_lt_top {U : Subgroup G} (hU : U < ⊤) :
    ∃ K : Subgroup G, IsCoatom K ∧ U ≤ K := by
  classical
  let s : Finset (Subgroup G) := Finset.univ.filter (fun K : Subgroup G => K < ⊤)
  have hU_mem : U ∈ s := by simp [s, hU]
  obtain ⟨K, hUK, hKmax⟩ := Finset.exists_le_maximal s hU_mem
  have hmax : Maximal (fun H : Subgroup G => H < ⊤) K := by
    simpa [s] using hKmax
  exact ⟨K, (isCoatom_iff_maximal_lt_top K).mpr hmax, hUK⟩

/-- A tuple fails to generate `G` exactly when all its entries lie in some maximal proper
subgroup. -/
theorem closure_ne_top_iff_exists_coatom (i : ℕ) (S : Fin i → G) :
    Subgroup.closure (Set.range S) ≠ ⊤ ↔ ∃ K ∈ maxSubs G, ∀ j, S j ∈ K := by
  classical
  constructor
  · intro hne
    have hlt : Subgroup.closure (Set.range S) < ⊤ := lt_top_iff_ne_top.mpr hne
    obtain ⟨K, hK, hle⟩ := exists_coatom_of_lt_top hlt
    refine ⟨K, ?_, fun j => hle (Subgroup.subset_closure ⟨j, rfl⟩)⟩
    simp only [maxSubs, mem_filter, mem_univ, true_and]
    exact hK
  · rintro ⟨K, hK, hSK⟩ htop
    have hKcoat : IsCoatom K := by
      simpa only [maxSubs, mem_filter, mem_univ, true_and] using hK
    have hle : Subgroup.closure (Set.range S) ≤ K := by
      rw [Subgroup.closure_le]
      rintro x ⟨j, rfl⟩
      exact hSK j
    have htopK : (⊤ : Subgroup G) ≤ K := htop ▸ hle
    exact hKcoat.ne_top (top_le_iff.mp htopK)

/-- The finite set of ordered `i`-tuples with every entry in `K`. -/
noncomputable def box (K : Subgroup G) (i : ℕ) : Finset (Fin i → G) := by
  classical
  exact Finset.univ.filter (fun S : Fin i → G => ∀ j, S j ∈ K)

/-- The equivalence between tuples in `G` whose entries lie in `K` and tuples valued in the
subgroup `K`. -/
def memFunEquiv (K : Subgroup G) (i : ℕ) :
    {S : Fin i → G // ∀ j, S j ∈ K} ≃ (Fin i → K) where
  toFun S j := ⟨S.1 j, S.2 j⟩
  invFun f := ⟨fun j => (f j : G), fun j => (f j).2⟩
  left_inv S := by
    apply Subtype.ext
    funext j
    rfl
  right_inv f := by
    funext j
    rfl

/-- The number of length-`i` tuples contained in `K` is `Nat.card K ^ i`. -/
theorem card_box (K : Subgroup G) (i : ℕ) :
    (box K i).card = (Nat.card K) ^ i := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  rw [box]
  rw [← Fintype.card_subtype (fun S : Fin i → G => ∀ j, S j ∈ K)]
  rw [Fintype.card_congr (memFunEquiv K i)]
  rw [Fintype.card_fun]
  simp [Nat.card_eq_fintype_card]

/-- Twice the cardinality of a proper subgroup is at most the cardinality of the finite group. -/
theorem two_mul_card_le_of_lt_top (K : Subgroup G) (hK : K < ⊤) :
    2 * Nat.card K ≤ Nat.card G := by
  classical
  have hne : K ≠ ⊤ := ne_of_lt hK
  have hidx : 2 ≤ K.index := by
    have h := Subgroup.one_lt_index_of_ne_top hne
    omega
  have hcard : Nat.card K * K.index = Nat.card G := K.card_mul_index
  calc 2 * Nat.card K ≤ K.index * Nat.card K := Nat.mul_le_mul_right _ hidx
    _ = Nat.card K * K.index := Nat.mul_comm _ _
    _ = Nat.card G := hcard

/-- The number of nongenerating `i`-tuples is at most the number of maximal proper subgroups
times `(card G / 2) ^ i`, with the bound taken in the reals. -/
theorem card_fail_le (i : ℕ) :
    ((failSet G i).card : ℝ)
      ≤ ((maxSubs G).card : ℝ) * (((Fintype.card G : ℝ) / 2) ^ i) := by
  classical
  have hsub : failSet G i ⊆ (maxSubs G).biUnion (fun K => box K i) := by
    intro S hS
    unfold failSet at hS
    simp only [mem_filter, mem_univ, true_and] at hS
    obtain ⟨K, hK, hSK⟩ := (closure_ne_top_iff_exists_coatom i S).mp hS
    exact mem_biUnion.mpr ⟨K, hK, by simp [box, hSK]⟩
  have hcardB : (failSet G i).card ≤ ∑ K ∈ maxSubs G, (box K i).card :=
    le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
  have hbox_le : ∀ K ∈ maxSubs G, ((box K i).card : ℝ) ≤
      (((Fintype.card G : ℝ) / 2) ^ i) := by
    intro K hK
    have hKcoat : IsCoatom K := by
      simpa only [maxSubs, mem_filter, mem_univ, true_and] using hK
    have hhalf : (Nat.card K : ℝ) ≤ (Fintype.card G : ℝ) / 2 := by
      have h := two_mul_card_le_of_lt_top K hKcoat.lt_top
      have h' : (2 : ℝ) * (Nat.card K : ℝ) ≤ (Fintype.card G : ℝ) := by
        rw [← Nat.card_eq_fintype_card (α := G)]
        exact_mod_cast h
      linarith
    rw [card_box, Nat.cast_pow]
    exact pow_le_pow_left₀ (by positivity) hhalf i
  have hsum : (∑ K ∈ maxSubs G, ((box K i).card : ℝ))
      ≤ ∑ _K ∈ maxSubs G, (((Fintype.card G : ℝ) / 2) ^ i) :=
    Finset.sum_le_sum hbox_le
  calc ((failSet G i).card : ℝ)
      ≤ ((∑ K ∈ maxSubs G, (box K i).card : ℕ) : ℝ) := by
        exact_mod_cast hcardB
    _ = ∑ K ∈ maxSubs G, ((box K i).card : ℝ) := by push_cast; ring
    _ ≤ ∑ _K ∈ maxSubs G, (((Fintype.card G : ℝ) / 2) ^ i) := hsum
    _ = ((maxSubs G).card : ℝ) * (((Fintype.card G : ℝ) / 2) ^ i) := by
        simp [Finset.sum_const, nsmul_eq_mul]

/-- The number of length-`i` tuples in `G` is `Fintype.card G ^ i`. -/
theorem card_univ_fun (i : ℕ) : Fintype.card (Fin i → G) = (Fintype.card G) ^ i := by
  rw [Fintype.card_fun]
  simp

/-- The generation probability is the cardinality of `genSet G i` divided by the total tuple
count. -/
theorem genProb_eq_card_genSet (i : ℕ) :
    genProb G i = ((genSet G i).card : ℝ) / (Fintype.card G : ℝ) ^ i := by
  classical
  unfold genProb genSet
  rfl

/-- The counts of generating and nongenerating tuples add to the total tuple count. -/
theorem genSet_card_add_failSet_card (i : ℕ) :
    (genSet G i).card + (failSet G i).card = (Fintype.card G) ^ i := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin i → G)))
    (p := fun S : Fin i → G => Subgroup.closure (Set.range S) = ⊤)
  simpa [genSet, failSet, card_univ_fun] using h

/-- The generation probability is one minus the fraction of nongenerating tuples. -/
theorem genProb_eq_one_sub_fail (i : ℕ) :
    genProb G i
      = 1 - ((failSet G i).card : ℝ)
          / (Fintype.card G : ℝ) ^ i := by
  classical
  have hsplit := genSet_card_add_failSet_card (G := G) i
  have hsub : (failSet G i).card ≤ (Fintype.card G) ^ i := by
    rw [← hsplit]
    exact Nat.le_add_left _ _
  have hgen : (genSet G i).card = (Fintype.card G) ^ i - (failSet G i).card := by
    omega
  rw [genProb_eq_card_genSet i, hgen]
  have hCpos : (0 : ℝ) < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos
  have hCne : (Fintype.card G : ℝ) ≠ 0 := ne_of_gt hCpos
  have hden : (Fintype.card G : ℝ) ^ i ≠ 0 := pow_ne_zero i hCne
  rw [Nat.cast_sub hsub, Nat.cast_pow]
  rw [sub_div, div_self hden]

/-- The generation probability for `i` samples is at least one minus `card (maxSubs G) * (1 / 2)
^ i`. See [RoettelerBeth1998]. -/
theorem genProb_ge_one_sub_maxSubs (i : ℕ) :
    1 - ((maxSubs G).card : ℝ) * ((1 / 2 : ℝ) ^ i) ≤ genProb G i := by
  classical
  have hCpos : (0 : ℝ) < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos
  have hCne : (Fintype.card G : ℝ) ≠ 0 := ne_of_gt hCpos
  have hratio : (((Fintype.card G : ℝ) / 2) ^ i) / (Fintype.card G : ℝ) ^ i
      = (1 / 2 : ℝ) ^ i := by
    have h1 : (Fintype.card G : ℝ) / 2 = (Fintype.card G : ℝ) * (1 / 2) := by ring
    rw [h1, mul_pow]
    exact mul_div_cancel_left₀ _ (pow_ne_zero i hCne)
  have hdiv : ((failSet G i).card : ℝ) / (Fintype.card G : ℝ) ^ i
      ≤ ((maxSubs G).card : ℝ) * ((1 / 2 : ℝ) ^ i) := by
    calc ((failSet G i).card : ℝ) / (Fintype.card G : ℝ) ^ i
        ≤ (((maxSubs G).card : ℝ) * (((Fintype.card G : ℝ) / 2) ^ i))
            / (Fintype.card G : ℝ) ^ i := by
          gcongr
          exact card_fail_le i
      _ = ((maxSubs G).card : ℝ)
            * ((((Fintype.card G : ℝ) / 2) ^ i) / (Fintype.card G : ℝ) ^ i) := by ring
      _ = ((maxSubs G).card : ℝ) * ((1 / 2 : ℝ) ^ i) := by rw [hratio]
  rw [genProb_eq_one_sub_fail i]
  linarith

/-- If `G` has at most `2 ^ d` maximal proper subgroups and `3 * d ≤ j`, then `4 * j` uniform
independent samples generate `G` with probability at least `1 - (1 / 2) ^ j`. This gives a
conditional sampling bound in the setting of Lemma 6.3 of [RoettelerBeth1998]. -/
theorem genProb_ge_corrected (d j : ℕ)
    (hM : (maxSubs G).card ≤ 2 ^ d) (hj : 3 * d ≤ j) :
    1 - (1 / 2 : ℝ) ^ j ≤ genProb G (4 * j) := by
  classical
  have hmain := genProb_ge_one_sub_maxSubs (G := G) (i := 4 * j)
  have hM' : ((maxSubs G).card : ℝ) ≤ (2 : ℝ) ^ d := by exact_mod_cast hM
  have h2d : (2 : ℝ) ^ d ≤ (2 : ℝ) ^ (3 * j) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hpow4 : (2 : ℝ) ^ (4 * j) = (2 : ℝ) ^ (3 * j) * (2 : ℝ) ^ j := by
    rw [show 4 * j = 3 * j + j by omega, pow_add]
  have harith : (2 : ℝ) ^ (3 * j) * (1 / 2 : ℝ) ^ (4 * j) = (1 / 2 : ℝ) ^ j := by
    rw [one_div, inv_pow, hpow4, mul_inv_rev]
    field_simp
    rw [← mul_pow]
    norm_num
  have key : ((maxSubs G).card : ℝ) * ((1 / 2 : ℝ) ^ (4 * j))
      ≤ (1 / 2 : ℝ) ^ j := by
    calc ((maxSubs G).card : ℝ) * ((1 / 2 : ℝ) ^ (4 * j))
        ≤ (2 : ℝ) ^ (3 * j) * ((1 / 2 : ℝ) ^ (4 * j)) := by
          gcongr
          exact le_trans hM' h2d
      _ = (1 / 2 : ℝ) ^ j := harith
  linarith

/-- The corrected generation probability bound applies to a finite subgroup `U` when its number
of maximal proper subgroups is at most `2 ^ d` and `3 * d ≤ j`. See [RoettelerBeth1998]. -/
theorem subgroup_genProb_ge_corrected (U : Subgroup G) [Fintype U] (d j : ℕ)
    (hM : (maxSubs U).card ≤ 2 ^ d) (hj : 3 * d ≤ j) :
    1 - (1 / 2 : ℝ) ^ j ≤ genProb U (4 * j) :=
  genProb_ge_corrected d j hM hj

/-- The corrected generation probability bound applies to `Wreath n` when its number of maximal
proper subgroups is at most `2 ^ d` and `3 * d ≤ j`. See [RoettelerBeth1998]. -/
theorem wreath_genProb_ge_corrected (n d j : ℕ)
    (hM : (maxSubs (Wreath n)).card ≤ 2 ^ d) (hj : 3 * d ≤ j) :
    1 - (1 / 2 : ℝ) ^ j ≤ genProb (Wreath n) (4 * j) :=
  genProb_ge_corrected d j hM hj

end Qatlib.Papers.NonabelianHSP98.MainResults.Lemma63
