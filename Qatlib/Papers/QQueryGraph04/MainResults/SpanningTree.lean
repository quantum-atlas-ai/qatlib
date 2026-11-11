/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Relation
import Mathlib.Order.Basic
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Disjoint
import Mathlib.Order.Lattice
import Mathlib.Order.RelClasses
import Mathlib.Tactic
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Qatlib.Papers.QQueryGraph04.MainResults.Model.Basic
import Qatlib.Papers.QQueryGraph04.MainResults.Model.SupportBounds
import Qatlib.Papers.QQueryGraph04.MainResults.ProblemDefs

/-!
# Spanning-tree cost and component bounds

This module proves numerical cost and error estimates for Borůvka and connectivity expressions,
and establishes the existence of a minimum-weight spanning tree from a supplied spanning tree.
It also constructs a partition into connected sets satisfying `DegreeBound` and bounds the
associated sum of square-root degree costs.

The source paper is [DurrEtAl2006].

## Main statements

* `exists_min_spanning_tree`: If a finite graph possesses a spanning tree, it possesses a
  spanning tree of minimum total natural-number edge weight.
* `lemma10_component_partition`: For degrees given by symmetrized adjacency, the vertices
  possess a pairwise disjoint covering by nonempty connected finite sets satisfying
  `DegreeBound`, with at most as many parts as vertices.
* `theorem9_query_cost`: The matrix-connectivity cost expression is at most 2n√n.

## References

* [Dürr et al., 2006][DurrEtAl2006]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.QQueryGraph04.MainResults.SpanningTree

open Finset
open Qatlib.Papers.QQueryGraph04.MainResults.Model
open Qatlib.Papers.QQueryGraph04.MainResults.ProblemDefs

/-- The accumulated Borůvka phase error is at most 1/4 [DurrEtAl2006]. -/
theorem theorem8_error (M : ℕ) : boruvkaError M ≤ 1 / 4 :=
  boruvkaError_le M

/-- For the given phase count and graph sizes, a positive constant bounds the Borůvka cost by
that constant times √(nm) [DurrEtAl2006]. -/
theorem theorem8_array_cost (M n m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ boruvkaCost M n m ≤ C * Real.sqrt ((n : ℝ) * (m : ℝ)) := by
  refine ⟨24, by norm_num, ?_⟩
  have hA : (0 : ℝ) ≤ (n : ℝ) * (m : ℝ) := by positivity
  have hterm : ∀ ℓ : ℕ, boruvkaIterCost n m ℓ =
      ((ℓ : ℝ) + 3) * (Real.sqrt ((n : ℝ) * (m : ℝ)) * (1 / Real.sqrt 2) ^ ℓ) := by
    intro ℓ
    unfold boruvkaIterCost
    rw [sqrt_div_pow_two ((n : ℝ) * (m : ℝ)) hA ℓ]
  unfold boruvkaCost
  calc (∑ ℓ ∈ Finset.range M, boruvkaIterCost n m ℓ)
      = ∑ ℓ ∈ Finset.range M,
          ((ℓ : ℝ) + 3) * (Real.sqrt ((n : ℝ) * (m : ℝ)) * (1 / Real.sqrt 2) ^ ℓ) :=
        Finset.sum_congr rfl fun ℓ _ => hterm ℓ
    _ = Real.sqrt ((n : ℝ) * (m : ℝ)) *
          ∑ ℓ ∈ Finset.range M, ((ℓ : ℝ) + 3) * (1 / Real.sqrt 2) ^ ℓ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun ℓ _ => by ring
    _ ≤ Real.sqrt ((n : ℝ) * (m : ℝ)) *
          ∑ ℓ ∈ Finset.range M, ((ℓ : ℝ) + 3) * (3 / 4 : ℝ) ^ ℓ := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        apply Finset.sum_le_sum
        intro ℓ _
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (by positivity) inv_sqrt_two_le_three_quarters ℓ
    _ ≤ Real.sqrt ((n : ℝ) * (m : ℝ)) * 24 := by
        exact mul_le_mul_of_nonneg_left (boruvkaGeomSum_le M) (Real.sqrt_nonneg _)
    _ = 24 * Real.sqrt ((n : ℝ) * (m : ℝ)) := by ring

/-- With m = n(n − 1), a positive constant bounds the Borůvka cost by that constant times n√n
[DurrEtAl2006]. -/
theorem theorem8_matrix_cost (M n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      boruvkaCost M n (n * (n - 1)) ≤ C * (n : ℝ) * Real.sqrt (n : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := theorem8_array_cost M n (n * (n - 1))
  refine ⟨C, hC, hbound.trans ?_⟩
  have hnm : ((n : ℝ) * ((n * (n - 1) : ℕ) : ℝ)) ≤ (n : ℝ) ^ 3 := by
    have hcast : ((n * (n - 1) : ℕ) : ℝ) ≤ (n : ℝ) * (n : ℝ) := by
      have hle : n * (n - 1) ≤ n * n := Nat.mul_le_mul_left n (Nat.sub_le n 1)
      calc ((n * (n - 1) : ℕ) : ℝ) ≤ ((n * n : ℕ) : ℝ) := by exact_mod_cast hle
        _ = (n : ℝ) * (n : ℝ) := by push_cast; ring
    calc (n : ℝ) * ((n * (n - 1) : ℕ) : ℝ) ≤ (n : ℝ) * ((n : ℝ) * (n : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hcast (Nat.cast_nonneg n)
      _ = (n : ℝ) ^ 3 := by ring
  have hsqrt : Real.sqrt ((n : ℝ) * ((n * (n - 1) : ℕ) : ℝ)) ≤ (n : ℝ) * Real.sqrt (n : ℝ) := by
    calc Real.sqrt ((n : ℝ) * ((n * (n - 1) : ℕ) : ℝ)) ≤ Real.sqrt ((n : ℝ) ^ 3) :=
          Real.sqrt_le_sqrt hnm
      _ = (n : ℝ) * Real.sqrt (n : ℝ) := by
          rw [show (n : ℝ) ^ 3 = (n : ℝ) ^ 2 * (n : ℝ) by ring,
            Real.sqrt_mul (by positivity), Real.sqrt_sq (Nat.cast_nonneg n)]
  calc C * Real.sqrt ((n : ℝ) * ((n * (n - 1) : ℕ) : ℝ))
      ≤ C * ((n : ℝ) * Real.sqrt (n : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hsqrt hC.le
    _ = C * (n : ℝ) * Real.sqrt (n : ℝ) := by ring

/-- If a finite graph possesses a spanning tree, it possesses a spanning tree of minimum total
natural-number edge weight [DurrEtAl2006]. -/
theorem exists_min_spanning_tree {n : ℕ} (adj : Fin n → Fin n → Bool)
    (w : Fin n → Fin n → ℕ) (h : ∃ T, IsSpanningTree adj T) :
    ∃ T, IsMST adj w T := by
  classical
  let S := (Finset.univ : Finset (Finset (Fin n × Fin n))).filter (fun T => IsSpanningTree adj T)
  have hS : S.Nonempty := by
    obtain ⟨T, hT⟩ := h
    exact ⟨T, by simp [S, hT]⟩
  obtain ⟨T, hT, hmin⟩ := Finset.exists_min_image S (edgeWeight w) hS
  refine ⟨T, ?_, fun S' hS' => ?_⟩
  · simpa [S] using (Finset.mem_filter.mp hT).2
  · exact hmin S' (by simp [S, hS'])

/-- The matrix-connectivity cost expression is at most 2n√n [DurrEtAl2006]. -/
theorem theorem9_query_cost (n : ℕ) :
    matrixConnectivityCost n ≤ 2 * (n : ℝ) * Real.sqrt (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [matrixConnectivityCost]
  have h1 := sum_sqrt_div_range (N := n * n) (n := n - 1)
  have hcast : ((n * n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by push_cast; ring
  have hsub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  simp only [hcast, hsub] at h1
  have hcost : matrixConnectivityCost n =
      ∑ j ∈ Finset.range (n - 1), Real.sqrt (((n : ℝ) ^ 2) / ((j : ℝ) + 1)) := rfl
  rw [hcost]
  have hmono : Real.sqrt (((n : ℝ) ^ 2) * ((n : ℝ) - 1)) ≤ Real.sqrt ((n : ℝ) ^ 3) := by
    apply Real.sqrt_le_sqrt
    nlinarith
  have hsqrt3 : Real.sqrt ((n : ℝ) ^ 3) = (n : ℝ) * Real.sqrt (n : ℝ) := by
    rw [show (n : ℝ) ^ 3 = (n : ℝ) ^ 2 * (n : ℝ) by ring]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  calc matrixConnectivityCost n
      = ∑ j ∈ Finset.range (n - 1), Real.sqrt (((n : ℝ) ^ 2) / ((j : ℝ) + 1)) := rfl
    _ ≤ 2 * Real.sqrt (((n : ℝ) ^ 2) * ((n : ℝ) - 1)) := by
        have hcast2 : ∀ j : ℕ, ((n * n : ℕ) : ℝ) = (n : ℝ) ^ 2 := fun _ => hcast
        simpa only [hcast2] using h1
    _ ≤ 2 * Real.sqrt ((n : ℝ) ^ 3) := by linarith [hmono]
    _ = 2 * (n : ℝ) * Real.sqrt (n : ℝ) := by rw [hsqrt3]; ring

/-- For degrees given by symmetrized adjacency, the vertices possess a pairwise disjoint
covering by nonempty connected finite sets satisfying `DegreeBound`, with at most as many
parts as vertices [DurrEtAl2006]. -/
theorem lemma10_component_partition {V : Type*} [Fintype V] [DecidableEq V]
    (adj : V → V → Bool) (deg : V → ℕ)
    (hdeg : ∀ v, deg v = (Finset.univ.filter fun w => (adj v w || adj w v)).card) :
    ∃ parts : Finset (Finset V),
      (∀ C ∈ parts, C.Nonempty) ∧
      (∀ C ∈ parts, ConnectedOn adj C) ∧
      (∀ C ∈ parts, DegreeBound deg C) ∧
      (∀ v : V, ∃ C ∈ parts, v ∈ C) ∧
      (∀ C ∈ parts, ∀ C' ∈ parts, C ≠ C' → Disjoint C C') ∧
      (parts.card : ℕ) ≤ Fintype.card V := by
  classical

  let r : V → V → Prop := fun a b => (adj a b || adj b a) = true

  have hsymm : ∀ a b, r a b → r b a := by
    intro a b h
    show (adj b a || adj a b) = true
    rwa [Bool.or_comm]

  have hreach_symm : ∀ a b, Relation.ReflTransGen r a b → Relation.ReflTransGen r b a := by
    intro a b h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih =>
        exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single (hsymm _ _ hbc)) ih

  let compOf : V → Finset V :=
    fun v => Finset.univ.filter (fun w => Relation.ReflTransGen r v w)
  have hmem : ∀ v w, w ∈ compOf v ↔ Relation.ReflTransGen r v w := by
    intro v w
    simp [compOf]
  refine ⟨Finset.univ.image compOf, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro C hC
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hC
    exact ⟨v, (hmem v v).mpr Relation.ReflTransGen.refl⟩
  · rintro C hC u hu v hv
    obtain ⟨v0, _, rfl⟩ := Finset.mem_image.mp hC
    show Relation.ReflTransGen r u v
    exact (hreach_symm _ _ ((hmem v0 u).mp hu)).trans ((hmem v0 v).mp hv)
  · rintro C hC
    obtain ⟨v0, _, rfl⟩ := Finset.mem_image.mp hC
    have hsub : ∀ u ∈ compOf v0,
        (Finset.univ.filter (fun w => r u w)) ⊆ compOf v0 := by
      intro u hu w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      exact (hmem v0 w).mpr
        (Relation.ReflTransGen.trans ((hmem v0 u).mp hu) (Relation.ReflTransGen.single hw))
    unfold DegreeBound totalDegree
    calc ∑ u ∈ compOf v0, deg u
        = ∑ u ∈ compOf v0, (Finset.univ.filter (fun w => r u w)).card := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [hdeg u]
      _ ≤ ∑ u ∈ compOf v0, (compOf v0).card := by
          refine Finset.sum_le_sum fun u hu => ?_
          exact Finset.card_le_card (hsub u hu)
      _ = (compOf v0).card ^ 2 := by
          rw [Finset.sum_const, smul_eq_mul]
          ring
  · intro v
    exact ⟨compOf v, Finset.mem_image_of_mem _ (Finset.mem_univ v),
      (hmem v v).mpr Relation.ReflTransGen.refl⟩
  · rintro C hC C' hC' hne
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hC'
    refine Finset.disjoint_left.mpr fun w hwu hwv => hne ?_
    have huw : Relation.ReflTransGen r u w := (hmem u w).mp hwu
    have hvw : Relation.ReflTransGen r v w := (hmem v w).mp hwv
    have huv : Relation.ReflTransGen r u v := huw.trans (hreach_symm _ _ hvw)
    have hvu : Relation.ReflTransGen r v u := hvw.trans (hreach_symm _ _ huw)
    ext z
    constructor
    · intro hz
      exact (hmem v z).mpr (hvu.trans ((hmem u z).mp hz))
    · intro hz
      exact (hmem u z).mpr (huv.trans ((hmem v z).mp hz))
  · calc (Finset.univ.image compOf).card ≤ (Finset.univ : Finset V).card :=
          Finset.card_image_le
      _ = Fintype.card V := Finset.card_univ

/-- If each component satisfies `DegreeBound` and the sum of component cardinalities is at most
n, the sum of square roots of total component degrees is at most n [DurrEtAl2006]. -/
theorem theorem11_query_cost {ι V : Type*} [Fintype ι] (deg : V → ℕ)
    (C : ι → Finset V) (n : ℕ) (hbound : ∀ i, DegreeBound deg (C i))
    (hcover : (∑ i, (C i).card) ≤ n) :
    (∑ i, Real.sqrt ((totalDegree deg (C i) : ℝ))) ≤ (n : ℝ) := by
  exact_mod_cast sum_sqrt_totalDegree_le deg C n hbound hcover

end Qatlib.Papers.QQueryGraph04.MainResults.SpanningTree
