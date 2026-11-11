/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Lattice.Lemmas
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Defs
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
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
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
# Strong connectivity and tier estimates

This module proves directed-tree cost bounds and a strong-connectivity reduction through a DFS
edge set and selected outgoing edges. It formalizes tier sizes and cumulative counts with
`TierInv`, proves update estimates for successful and failed steps, and bounds weighted tier
failures and expected cost expressions.

The source paper is [DurrEtAl2006].

## Main statements

* `theorem13_strong_connectivity_reduction`: Under the stated edge inclusion, rooted DFS order,
  and outgoing-edge selection hypotheses, the original graph is strongly connected exactly when
  A ∪ B is strongly connected.
* `TierInv`: The tier family has the specified lowest and highest nonempty tiers, disjoint
  tiers, individual size bounds, and cumulative size bounds.
* `lemma17_expected_cost`: For each n there is a positive constant uniformly bounding finite
  weighted tier costs by that constant times √n when the nonnegative weights are at most
  (1/2)^(2ⁱ).

## References

* [Dürr et al., 2006][DurrEtAl2006]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.QQueryGraph04.MainResults.StrongConnectivity

open Finset
open Qatlib.Papers.QQueryGraph04.MainResults.Model
open Qatlib.Papers.QQueryGraph04.MainResults.ProblemDefs

/-- Bounds the directed-tree cost by √(nmL) when the sums of the vertex parameters b and d are
at most n and m [DurrEtAl2006]. -/
theorem theorem12_query_cost {V : Type*} [Fintype V] (L : ℕ) (b d : V → ℕ) (n m : ℕ)
    (hb : (∑ u, b u) ≤ n) (hd : (∑ u, d u) ≤ m) :
    directedTreeCost L b d ≤ Real.sqrt ((n : ℝ) * (m : ℝ) * (L : ℝ)) := by
  have hterm : ∀ u, directedTreeVertexCost L (b u) (d u) =
      Real.sqrt (b u) * Real.sqrt ((d u : ℝ) * (L : ℝ)) := by
    intro u
    unfold directedTreeVertexCost
    rw [show (b u : ℝ) * (d u : ℝ) * (L : ℝ) =
        (b u : ℝ) * ((d u : ℝ) * (L : ℝ)) by ring,
      Real.sqrt_mul (Nat.cast_nonneg _)]
  unfold directedTreeCost
  calc (∑ u, directedTreeVertexCost L (b u) (d u))
      = ∑ u, Real.sqrt (b u) * Real.sqrt ((d u : ℝ) * (L : ℝ)) :=
        Finset.sum_congr rfl fun u _ => hterm u
    _ = ∑ u, Real.sqrt (b u) * Real.sqrt ((d u * L : ℕ) : ℝ) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Nat.cast_mul]
    _ ≤ Real.sqrt (∑ u, (b u : ℝ)) * Real.sqrt (∑ u, ((d u * L : ℕ) : ℝ)) :=
        sum_sqrt_mul_le Finset.univ b (fun u => d u * L)
    _ ≤ Real.sqrt (n : ℝ) * Real.sqrt ((L : ℝ) * (m : ℝ)) := by
        have hbsum : Real.sqrt (∑ u, (b u : ℝ)) ≤ Real.sqrt (n : ℝ) :=
          Real.sqrt_le_sqrt (by exact_mod_cast hb)
        have hdsum : (∑ u, ((d u * L : ℕ) : ℝ)) = (L : ℝ) * ∑ u, (d u : ℝ) := by
          push_cast
          rw [← Finset.sum_mul, mul_comm]
        have hd' : Real.sqrt (∑ u, ((d u * L : ℕ) : ℝ)) ≤
            Real.sqrt ((L : ℝ) * (m : ℝ)) := by
          rw [hdsum]
          exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (by exact_mod_cast hd)
            (Nat.cast_nonneg L))
        exact mul_le_mul hbsum hd' (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt ((n : ℝ) * (m : ℝ) * (L : ℝ)) := by
        rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (n : ℝ))]
        congr 1
        ring

/-- For n ≥ 1, the directed-tree error expression is at most 1/10 [DurrEtAl2006]. -/
theorem theorem12_error (n : ℕ) (hn : 1 ≤ n) : directedTreeError n ≤ 1 / 10 :=
  directedTreeError_le n hn

/-- For n ≥ 1, one minus the directed-tree error expression is at least 9/10 [DurrEtAl2006]. -/
theorem theorem12_success (n : ℕ) (hn : 1 ≤ n) :
    9 / 10 ≤ 1 - directedTreeError n := by
  have h := theorem12_error n hn
  linarith

/-- The Boolean directed adjacency relation determined by membership in a finite edge set. -/
def edgeRel {V : Type*} [DecidableEq V] (E : Finset (V × V)) : V → V → Bool :=
  fun a b => decide ((a, b) ∈ E)

/-- The relation `edgeRel E` holds exactly for ordered pairs belonging to `E`. -/
theorem edgeRel_iff {V : Type*} [DecidableEq V] (E : Finset (V × V)) (a b : V) :
    edgeRel E a b = true ↔ (a, b) ∈ E := by
  simp [edgeRel]

/-- A path using edges of A remains a path after adjoining the edge set B. -/
theorem reach_mono_left {V : Type*} [DecidableEq V] (A B : Finset (V × V)) {a b : V}
    (h : Reach (edgeRel A) a b) : Reach (edgeRel (A ∪ B)) a b :=
  Relation.ReflTransGen.mono (fun x y hxy => by
    rw [edgeRel] at hxy ⊢
    simp only [decide_eq_true_eq] at hxy ⊢
    exact Finset.mem_union.mpr (Or.inl hxy)) _ _ h

/-- If a vertex has an outgoing edge, one outgoing neighbor minimizes the natural-number order
function among all outgoing neighbors. -/
theorem exists_min_out {V : Type*} [Fintype V] [DecidableEq V]
    (adj : V → V → Bool) (ord : V → ℕ) {x : V} (h : ∃ y, adj x y = true) :
    ∃ w, adj x w = true ∧ ∀ y, adj x y = true → ord w ≤ ord y := by
  classical
  let S := (Finset.univ : Finset V).filter (fun y => adj x y = true)
  have hS : S.Nonempty := by
    obtain ⟨y, hy⟩ := h
    exact ⟨y, by simp [S, hy]⟩
  obtain ⟨w, hw, hmin⟩ := Finset.exists_min_image S ord hS
  refine ⟨w, (Finset.mem_filter.mp hw).2, fun y hy => hmin y ?_⟩
  simp [S, hy]

/-- A path starting at order at least i and ending below i contains an edge that crosses below
i, preceded by a path from the start [DurrEtAl2006]. -/
theorem exists_first_drop {α : Type*} {r : α → α → Prop} {ord : α → ℕ} (i : ℕ)
    {a b : α} (hab : Relation.ReflTransGen r a b) (ha : i ≤ ord a) (hb : ord b < i) :
    ∃ x y, Relation.ReflTransGen r a x ∧ r x y ∧ i ≤ ord x ∧ ord y < i := by
  by_contra hcon
  have hval : ∀ x y, Relation.ReflTransGen r a x → r x y → i ≤ ord x → i ≤ ord y := by
    intro x y hRx hxy hx
    by_contra hy
    exact hcon ⟨x, y, hRx, hxy, hx, not_le.mp hy⟩
  have hall : ∀ z, Relation.ReflTransGen r a z → i ≤ ord z := by
    intro z hz
    induction hz with
    | refl => exact ha
    | tail hz' hstep ih => exact hval _ _ hz' hstep ih
  exact absurd (hall b hab) (not_le.mpr hb)

/-- If all edges of A and B belong to the original graph, strong connectivity of their union
implies strong connectivity of the original graph [DurrEtAl2006]. -/
theorem theorem13_reduction_forward {V : Type*} [Fintype V] [DecidableEq V] (adj : V → V → Bool)
    (A B : Finset (V × V))
    (hA : ∀ e ∈ A, adj e.1 e.2 = true) (hB : ∀ e ∈ B, adj e.1 e.2 = true) :
    StronglyConnectedOn (edgeRel (A ∪ B)) (Finset.univ : Finset V) →
      StronglyConnectedOn adj (Finset.univ : Finset V) := by
  intro hSC u hu v hv
  have hmono : ∀ a b : V, edgeRel (A ∪ B) a b = true → adj a b = true := by
    intro a b hab
    have hmem : (a, b) ∈ A ∪ B := (edgeRel_iff (A ∪ B) a b).mp hab
    rcases Finset.mem_union.mp hmem with h | h
    · exact hA _ h
    · exact hB _ h
  obtain ⟨h1, h2⟩ := hSC u hu v hv
  exact ⟨Relation.ReflTransGen.mono (fun a b hab => hmono a b hab) _ _ h1,
    Relation.ReflTransGen.mono (fun a b hab => hmono a b hab) _ _ h2⟩

/-- Under the injective rooted order, DFS reachability, and minimum-outgoing-edge hypotheses,
strong connectivity of the original graph implies strong connectivity of A ∪ B
[DurrEtAl2006]. -/
theorem theorem13_reduction_backward {V : Type*} [Fintype V] [DecidableEq V]
    (adj : V → V → Bool) (A B : Finset (V × V)) (v0 : V) (ord : V → ℕ)
    (hord : Function.Injective ord) (hroot : ∀ w, ord v0 ≤ ord w)
    (hDFS : ∀ u v, ord u < ord v → Reach adj u v → Reach (edgeRel A) u v)
    (hB : ∀ v w, v ≠ v0 → adj v w = true →
      (∀ w', adj v w' = true → ord w ≤ ord w') → (v, w) ∈ B) :
    StronglyConnectedOn adj (Finset.univ : Finset V) →
      StronglyConnectedOn (edgeRel (A ∪ B)) (Finset.univ : Finset V) := by
  classical
  intro hSC

  have hToRoot : ∀ x : V, Reach (edgeRel (A ∪ B)) x v0 := by
    intro x
    by_contra hx
    let S := (Finset.univ : Finset V).filter (fun z => ¬ Reach (edgeRel (A ∪ B)) z v0)
    have hxS : x ∈ S := by simp [S, hx]
    obtain ⟨x0, hx0S, hmin⟩ := Finset.exists_min_image S ord ⟨x, hxS⟩
    have hx0bad : ¬ Reach (edgeRel (A ∪ B)) x0 v0 := by
      simpa [S] using (Finset.mem_filter.mp hx0S).2
    have hx0ne : x0 ≠ v0 := by
      intro h
      apply hx0bad
      rw [h]
      exact Relation.ReflTransGen.refl
    have hv0lt : ord v0 < ord x0 := by
      rcases lt_or_eq_of_le (hroot x0) with h | h
      · exact h
      · exact absurd (hord h).symm hx0ne
    have hpath : Reach adj x0 v0 := (hSC x0 (Finset.mem_univ _) v0 (Finset.mem_univ _)).1
    have hx0out : ∃ y, adj x0 y = true := by
      rcases Relation.ReflTransGen.cases_head hpath with h | ⟨c, hac, _⟩
      · exact absurd h hx0ne
      · exact ⟨c, hac⟩
    obtain ⟨x, y, hRx, hstep, hix, hiy⟩ :=
      exists_first_drop (ord x0) hpath (le_refl (ord x0)) hv0lt
    obtain ⟨w, hwx, hwmin⟩ := exists_min_out adj ord (x := x) ⟨y, hstep⟩
    have hwlt : ord w < ord x0 := lt_of_le_of_lt (hwmin y hstep) hiy
    have hgood : Reach (edgeRel (A ∪ B)) w v0 := by
      by_contra hcon
      exact absurd hwlt (not_lt.mpr (hmin w (by simp [S, hcon])))
    rcases lt_or_eq_of_le hix with hlt | heq
    · have hApath : Reach (edgeRel A) x0 x := hDFS x0 x hlt hRx
      have hxne : x ≠ v0 := by
        intro h
        rw [h] at hlt
        omega
      have hBmem : (x, w) ∈ B := hB x w hxne hwx hwmin
      have hstepB : edgeRel (A ∪ B) x w = true := by
        rw [edgeRel]
        simp only [decide_eq_true_eq]
        exact Finset.mem_union.mpr (Or.inr hBmem)
      exact hx0bad ((reach_mono_left A B hApath).tail hstepB |>.trans hgood)
    · have hxx0 : x = x0 := hord heq.symm
      have hwx0 : adj x0 w = true := by rw [← hxx0]; exact hwx
      have hwmin0 : ∀ w', adj x0 w' = true → ord w ≤ ord w' := by
        intro w' hw'
        rw [← hxx0] at hw'
        exact hwmin w' hw'
      have hBmem : (x0, w) ∈ B := hB x0 w hx0ne hwx0 hwmin0
      have hstepB : edgeRel (A ∪ B) x0 w = true := by
        rw [edgeRel]
        simp only [decide_eq_true_eq]
        exact Finset.mem_union.mpr (Or.inr hBmem)
      exact hx0bad (Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single
          (r := fun a b : V => edgeRel (A ∪ B) a b = true) hstepB)
        hgood)

  have hFromRoot : ∀ x : V, Reach (edgeRel (A ∪ B)) v0 x := by
    intro x
    by_cases hx : x = v0
    · subst hx
      exact Relation.ReflTransGen.refl
    · have hlt : ord v0 < ord x := by
        rcases lt_or_eq_of_le (hroot x) with h | h
        · exact h
        · exact absurd (hord h).symm hx
      exact reach_mono_left A B
        (hDFS v0 x hlt (hSC v0 (Finset.mem_univ _) x (Finset.mem_univ _)).1)
  intro u _ v _
  exact ⟨(hToRoot u).trans (hFromRoot v), (hToRoot v).trans (hFromRoot u)⟩

/-- Under the stated edge inclusion, rooted DFS order, and outgoing-edge selection hypotheses,
the original graph is strongly connected exactly when A ∪ B is strongly connected
[DurrEtAl2006]. -/
theorem theorem13_strong_connectivity_reduction {V : Type*} [Fintype V] [DecidableEq V]
    (adj : V → V → Bool) (A B : Finset (V × V)) (v0 : V) (ord : V → ℕ)
    (hord : Function.Injective ord) (hroot : ∀ w, ord v0 ≤ ord w)
    (hA : ∀ e ∈ A, adj e.1 e.2 = true) (hBsub : ∀ e ∈ B, adj e.1 e.2 = true)
    (hDFS : ∀ u v, ord u < ord v → Reach adj u v → Reach (edgeRel A) u v)
    (hB : ∀ v w, v ≠ v0 → adj v w = true →
      (∀ w', adj v w' = true → ord w ≤ ord w') → (v, w) ∈ B) :
    StronglyConnectedOn adj (Finset.univ : Finset V) ↔
      StronglyConnectedOn (edgeRel (A ∪ B)) (Finset.univ : Finset V) :=
  ⟨theorem13_reduction_backward adj A B v0 ord hord hroot hDFS hB,
    theorem13_reduction_forward adj A B hA hBsub⟩

/-- If every edge strictly increases the order function, reachability weakly increases it
[DurrEtAl2006]. -/
theorem dfs_ord_mono {V : Type*} (A : V → V → Bool) (ord : V → ℕ)
    (hmono : ∀ a b, A a b = true → ord a < ord b) {u v : V}
    (h : Reach A u v) : ord u ≤ ord v := by
  induction h with
  | refl => exact le_refl _
  | tail _ hbc ih => exact le_trans ih (le_of_lt (hmono _ _ hbc))

/-- Under the stated DFS order, edge, tree-comparability, and reachable-vertex order hypotheses,
a path from an earlier vertex to a later vertex yields reachability in the DFS relation
[DurrEtAl2006]. -/
theorem lemma14_dfs_subtree {V : Type*} [Fintype V] [DecidableEq V]
    (adj : V → V → Bool) (A : V → V → Bool) (ord : V → ℕ)
    (hInj : Function.Injective ord) (hmono : ∀ a b, A a b = true → ord a < ord b)
    (hEdge : ∀ a b, adj a b = true → ord a < ord b → Reach A a b)
    (hEdgeBack : ∀ a b, adj a b = true → ord b < ord a → Reach A b a)
    (htree : ∀ a b c, Reach A a c → Reach A b c → Reach A a b ∨ Reach A b a)
    (l l' : V) (hll' : ord l < ord l') (hpath : Reach adj l l')
    (hwhite : ∀ z, Reach adj l z → z ≠ l → ord l ≤ ord z) :
    Reach A l l' := by

  have hreach_ord : ∀ a b, Reach A a b → ord a ≤ ord b := by
    intro a b h
    induction h with
    | refl => exact le_refl _
    | tail _ hbc ih => exact le_trans ih (le_of_lt (hmono _ _ hbc))

  have hmain : ∀ z, Reach adj l z → Reach A l z := by
    intro z hz
    induction hz with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c hz' hstep ih =>
        by_cases hcl : c = l
        · subst hcl
          exact Relation.ReflTransGen.refl
        · rcases lt_trichotomy (ord b) (ord c) with hlt | heq | hgt
          · exact Relation.ReflTransGen.trans ih (hEdge b c hstep hlt)
          · have hbc : b = c := hInj heq
            rwa [hbc] at ih
          · have hwhite_c : ord l ≤ ord c :=
              hwhite c (Relation.ReflTransGen.tail hz' hstep) hcl
            rcases htree l c b ih (hEdgeBack b c hstep hgt) with h | h
            · exact h
            · have hcle : ord c ≤ ord l := hreach_ord c l h
              exact absurd (hInj (le_antisymm hcle hwhite_c)) hcl
  exact hmain l' hpath

/-- The sum of tier cardinalities from tier zero through tier j. -/
noncomputable def tierTotal {V : Type*} (T : ℕ → Finset V) (j : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (j + 1), (T i).card

/-- The tier family has lowest and highest nonempty tiers, satisfies the top-tier size bound,
and satisfies the cumulative size bounds between them. -/
def TierInvariant {V : Type*} (T : ℕ → Finset V) : Prop :=
  ∃ k ℓ : ℕ, k ≤ ℓ ∧ (T k).Nonempty ∧ (T ℓ).Nonempty ∧
    (∀ i, i < k → T i = ∅) ∧ (∀ j, ℓ < j → T j = ∅) ∧
    2 ^ (ℓ - 1) ≤ (T ℓ).card ∧
    ∀ j, k ≤ j → j < ℓ → 2 ^ j ≤ tierTotal T j

/-- From `TierInvariant`, obtains indices k and ℓ such that k < ℓ implies tier k has at least 2ᵏ
elements and all lower tiers have fewer than their respective powers of two [DurrEtAl2006]. -/
theorem lemma15_chosen_index {V : Type*} (T : ℕ → Finset V)
    (hinv : TierInvariant T) :
    ∃ k ℓ : ℕ, k < ℓ → 2 ^ k ≤ (T k).card ∧ ∀ j, j < k → (T j).card < 2 ^ j := by
  obtain ⟨k, ℓ, _hkℓ, _hkne, _hℓne, hbelow, _habove, _hge, htj⟩ := hinv
  refine ⟨k, ℓ, fun hkl => ⟨?_, ?_⟩⟩
  · have hsum : tierTotal T k = (T k).card := by
      unfold tierTotal
      rw [Finset.sum_range_succ]
      have hzero : (∑ i ∈ Finset.range k, (T i).card) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [hbelow i (Finset.mem_range.mp hi), Finset.card_empty]
      rw [hzero, zero_add]
    have := htj k (le_refl k) hkl
    rwa [hsum] at this
  · intro j hj
    rw [hbelow j hj, Finset.card_empty]
    exact pow_pos (by norm_num) j

/-- If `TierInvariant` holds and every tier is below its power-of-two threshold, exactly one
tier is nonempty, with cardinality between 2^(i − 1) and 2ⁱ [DurrEtAl2006]. -/
theorem lemma15_stop_state {V : Type*} (T : ℕ → Finset V)
    (hinv : TierInvariant T) (hstop : ∀ i, (T i).card < 2 ^ i) :
    ∃ i : ℕ, (T i).Nonempty ∧ 2 ^ (i - 1) ≤ (T i).card ∧ (T i).card < 2 ^ i ∧
      ∀ j, j ≠ i → T j = ∅ := by
  obtain ⟨k, ℓ, hkℓ, hkne, hℓne, hbelow, habove, hge, htj⟩ := hinv
  have hk_eq : k = ℓ := by
    by_contra hne
    have hklt : k < ℓ := lt_of_le_of_ne hkℓ hne
    have hsum : tierTotal T k = (T k).card := by
      unfold tierTotal
      rw [Finset.sum_range_succ]
      have hzero : (∑ i ∈ Finset.range k, (T i).card) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [hbelow i (Finset.mem_range.mp hi), Finset.card_empty]
      rw [hzero, zero_add]
    have hle : 2 ^ k ≤ (T k).card := by
      have := htj k (le_refl k) hklt
      rwa [hsum] at this
    have hlt := hstop k
    omega
  refine ⟨ℓ, hℓne, hge, hstop ℓ, ?_⟩
  intro j hj
  rcases lt_or_gt_of_ne hj with h | h
  · exact hbelow j (by omega)
  · exact habove j h

variable {V : Type*}

/-- Tier k is nonempty and every lower tier is empty. -/
def IsLowestNonempty (T : ℕ → Finset V) (k : ℕ) : Prop :=
  (T k).Nonempty ∧ ∀ j, j < k → T j = ∅

/-- Tier `ell` is nonempty and every higher tier is empty. -/
def IsTopNonempty (T : ℕ → Finset V) (ell : ℕ) : Prop :=
  (T ell).Nonempty ∧ ∀ j, ell < j → T j = ∅

/-- Distinct tiers are pairwise disjoint. -/
def TiersDisjoint (T : ℕ → Finset V) : Prop :=
  ∀ i j, i ≠ j → Disjoint (T i) (T j)

/-- Every nonempty tier j has cardinality at least 2^(j − 1). -/
def TierSized (T : ℕ → Finset V) : Prop :=
  ∀ j, T j = ∅ ∨ 2 ^ (j - 1) ≤ (T j).card

/-- Between the lowest and highest specified tiers, the cumulative cardinality through j is at
least 2ʲ. -/
def TierCumul (T : ℕ → Finset V) (k ell : ℕ) : Prop :=
  ∀ j, k ≤ j → j < ell → 2 ^ j ≤ tierTotal T j

/-- The tier family has the specified lowest and highest nonempty tiers, disjoint tiers,
individual size bounds, and cumulative size bounds. -/
structure TierInv (T : ℕ → Finset V) (k ell : ℕ) : Prop where
  hk : k ≤ ell
  hlow : IsLowestNonempty T k
  htop : IsTopNonempty T ell
  hdisj : TiersDisjoint T
  hsize : TierSized T
  hcum : TierCumul T k ell

/-- The selected subset R lies in tier i and is either the entire tier or has size 2ⁱ in a tier
of size at least 2^(i + 1), with tier i of size at least 2ⁱ. -/
def StepData (T : ℕ → Finset V) (i : ℕ) (R : Finset V) : Prop :=
  R ⊆ T i ∧ 2 ^ i ≤ (T i).card ∧
    (R = T i ∨ (R.card = 2 ^ i ∧ 2 ^ (i + 1) ≤ (T i).card))

/-- The successful tier update joins R and v to tier zero and removes R from tier i when i is
positive. -/
noncomputable def tierStepSucc [DecidableEq V] (T : ℕ → Finset V) (i : ℕ) (R : Finset V)
    (v : V) : ℕ → Finset V :=
  fun j => if j = 0 then T 0 ∪ R ∪ {v} else if j = i then T i \ R else T j

/-- The failed tier update removes R from tier i and joins it to tier i + 1. -/
noncomputable def tierStepFail [DecidableEq V] (T : ℕ → Finset V) (i : ℕ)
    (R : Finset V) : ℕ → Finset V :=
  fun j => if j = i then T i \ R else if j = i + 1 then T (i + 1) ∪ R else T j

/-- A subset satisfying `StepData` has at least 2ⁱ elements. -/
theorem StepData.card_ge {T : ℕ → Finset V} {i : ℕ} {R : Finset V} (h : StepData T i R) :
    2 ^ i ≤ R.card := by
  rcases h.2.2 with rfl | ⟨hc, _⟩
  · exact h.2.1
  · rw [hc]

/-- A subset satisfying `StepData` has cardinality at most that of tier i. -/
theorem StepData.card_le {T : ℕ → Finset V} {i : ℕ} {R : Finset V} (h : StepData T i R) :
    R.card ≤ (T i).card := Finset.card_le_card h.1

/-- A subset satisfying `StepData` is the whole tier, or has size 2ⁱ while the tier has size at
least 2^(i + 1). -/
theorem StepData.eq_or_card {T : ℕ → Finset V} {i : ℕ} {R : Finset V}
    (h : StepData T i R) :
    R = T i ∨ (R.card = 2 ^ i ∧ 2 ^ (i + 1) ≤ (T i).card) := h.2.2

/-- If a valid step leaves a nonempty remainder in tier i, then the tier has size at least 2^(i
+ 1) and R has size 2ⁱ. -/
theorem StepData.proper_card [DecidableEq V] {T : ℕ → Finset V} {i : ℕ} {R : Finset V}
    (h : StepData T i R) (hne : T i \ R ≠ ∅) :
    2 ^ (i + 1) ≤ (T i).card ∧ R.card = 2 ^ i := by
  rcases h.eq_or_card with rfl | hc
  · exact absurd (Finset.sdiff_self (T i)) hne
  · exact ⟨hc.2, hc.1⟩

/-- The cumulative cardinality through tier zero equals the cardinality of tier zero. -/
theorem tierTotal_zero (T : ℕ → Finset V) : tierTotal T 0 = (T 0).card := by
  simp [tierTotal]

/-- The cumulative cardinality through tier j + 1 is the cumulative cardinality through j plus
the next tier size. -/
theorem tierTotal_succ (T : ℕ → Finset V) (j : ℕ) :
    tierTotal T (j + 1) = tierTotal T j + (T (j + 1)).card := by
  unfold tierTotal
  rw [Finset.sum_range_succ]

/-- Removing a finite subset subtracts its cardinality from the cardinality of the containing
set. -/
theorem card_sdiff_subset [DecidableEq V] {A B : Finset V} (h : B ⊆ A) :
    (A \ B).card = A.card - B.card := by
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr h]

/-- Tier zero after a successful update is T 0 ∪ R ∪ {v}. -/
theorem stepSucc_zero [DecidableEq V] (T : ℕ → Finset V) (i : ℕ) (R : Finset V) (v : V) :
    tierStepSucc T i R v 0 = T 0 ∪ R ∪ {v} := by
  simp [tierStepSucc]

/-- A positive tier after a successful update loses R exactly when its index equals i. -/
theorem stepSucc_pos [DecidableEq V] (T : ℕ → Finset V) (i : ℕ) (R : Finset V) (v : V)
    (j : ℕ) (hj : j ≠ 0) :
    tierStepSucc T i R v j = if j = i then T i \ R else T j := by
  simp only [tierStepSucc, if_neg hj]

/-- For disjoint tiers and valid step data, a failed update subtracts the size of R at tier i
and adds it at tier i + 1. -/
theorem stepFail_card [DecidableEq V] {T : ℕ → Finset V} {i : ℕ} {R : Finset V}
    (h : StepData T i R) (hdisj : TiersDisjoint T) (j : ℕ) :
    (tierStepFail T i R j).card =
      if j = i then (T i).card - R.card
      else if j = i + 1 then (T (i + 1)).card + R.card else (T j).card := by
  unfold tierStepFail
  by_cases h1 : j = i
  · rw [if_pos h1, if_pos h1, card_sdiff_subset h.1]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : j = i + 1
    · rw [if_pos h2, if_pos h2]
      have hdis : Disjoint (T (i + 1)) R :=
        (hdisj (i + 1) i (by omega)).mono_right h.1
      exact Finset.card_union_of_disjoint hdis
    · rw [if_neg h2, if_neg h2]

/-- For disjoint tiers, valid step data, and a fresh vertex v, a successful update increases the
cumulative size by one and also by the size of R below tier i [DurrEtAl2006]. -/
theorem stepSucc_total [DecidableEq V] {T : ℕ → Finset V} {i : ℕ} {R : Finset V} {v : V}
    (h : StepData T i R) (hdisj : TiersDisjoint T) (hv : ∀ j, v ∉ T j) (j : ℕ) :
    tierTotal (tierStepSucc T i R v) j =
      tierTotal T j + (if j < i then R.card else 0) + 1 := by
  induction j with
  | zero =>
      rw [tierTotal_zero, tierTotal_zero, stepSucc_zero]
      by_cases hi : i = 0
      · subst hi
        rw [Finset.union_eq_left.mpr h.1,
          Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr (hv 0)),
          Finset.card_singleton]
        simp
      · have hi0 : 0 < i := Nat.pos_of_ne_zero hi
        have hd0 : Disjoint (T 0) R := (hdisj 0 i (by omega)).mono_right h.1
        have hvR : v ∉ R := fun hm => hv i (h.1 hm)
        have hv0 : v ∉ T 0 ∪ R := by simp [Finset.mem_union, hv 0, hvR]
        rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hv0),
          Finset.card_union_of_disjoint hd0, Finset.card_singleton,
          if_pos hi0]
  | succ j ih =>
      rw [tierTotal_succ, tierTotal_succ, ih,
        stepSucc_pos T i R v (j + 1) (Nat.succ_ne_zero j)]
      have hRle : R.card ≤ (T i).card := h.card_le
      by_cases h1 : j + 1 = i
      · have hjt : j < i := by omega
        have hT : (T (j + 1)).card = (T i).card := by rw [h1]
        rw [if_pos h1, if_pos hjt, card_sdiff_subset h.1, hT,
          if_neg (by omega : ¬ j + 1 < i)]
        omega
      · rw [if_neg h1]
        by_cases h2 : j + 1 < i
        · have hjt : j < i := by omega
          rw [if_pos h2, if_pos hjt]
          omega
        · have hjt : ¬ j < i := by omega
          rw [if_neg h2, if_neg hjt]
          omega

/-- For disjoint tiers and valid step data, a failed update decreases the cumulative size by the
size of R exactly at index i [DurrEtAl2006]. -/
theorem stepFail_total [DecidableEq V] {T : ℕ → Finset V} {i : ℕ} {R : Finset V}
    (h : StepData T i R) (hdisj : TiersDisjoint T) (j : ℕ) :
    tierTotal (tierStepFail T i R) j = tierTotal T j - (if j = i then R.card else 0) := by
  induction j with
  | zero =>
      rw [tierTotal_zero, tierTotal_zero, stepFail_card h hdisj 0]
      rcases Nat.eq_zero_or_pos i with hi | hi
      · subst hi
        rw [if_pos rfl]
        simp
      · have h0 : ¬ (0 : ℕ) = i := by omega
        have h1 : ¬ (0 : ℕ) = i + 1 := by omega
        rw [if_neg h0, if_neg h1, if_neg h0]
        simp
  | succ j ih =>
      rw [tierTotal_succ, tierTotal_succ, ih, stepFail_card h hdisj (j + 1)]
      have hRle : R.card ≤ (T i).card := h.card_le
      by_cases h1 : j + 1 = i
      · have hji : ¬ j = i := by omega
        have hT : (T (j + 1)).card = (T i).card := by rw [h1]
        simp only [if_pos h1, if_neg hji, hT]
        omega
      · by_cases h2 : j + 1 = i + 1
        · have hji : j = i := by omega
          have hT : (T (j + 1)).card = (T (i + 1)).card := by rw [h2]
          have hsingle : (T i).card ≤ tierTotal T i := by
            unfold tierTotal
            exact Finset.single_le_sum (f := fun l => (T l).card) (fun l _ => Nat.zero_le _)
              (Finset.mem_range.mpr (Nat.lt_succ_self i))
          have hRt : R.card ≤ tierTotal T j := by
            rw [hji]
            exact le_trans h.card_le hsingle
          simp only [if_pos h2, if_pos hji, hT, if_neg h1]
          omega
        · have hji : ¬ j = i := by omega
          simp only [if_neg h1, if_neg h2, if_neg hji]
          omega

/-- The highest nonempty tier in `TierInv` has cardinality at least 2^(ell − 1). -/
theorem TierInv.card_top {T : ℕ → Finset V} {k ell : ℕ} (h : TierInv T k ell) :
    2 ^ (ell - 1) ≤ (T ell).card := by
  rcases h.hsize ell with he | hge
  · exact absurd he h.htop.1.ne_empty
  · exact hge

/-- The structured tier conditions `TierInv` imply `TierInvariant`. -/
theorem TierInv.toInvariant {T : ℕ → Finset V} {k ell : ℕ} (h : TierInv T k ell) :
    TierInvariant T := by
  exact ⟨k, ell, h.hk, h.hlow.1, h.htop.1, h.hlow.2, h.htop.2, h.card_top, h.hcum⟩

/-- A valid successful update below the top tier with a fresh vertex preserves the cumulative
power-of-two lower bounds at every index below the top tier [DurrEtAl2006]. -/
theorem tier_cumul_succ [DecidableEq V] {T : ℕ → Finset V} {k ell i : ℕ} {R : Finset V}
    {v : V} (h : TierInv T k ell) (hi : k ≤ i) (_hielt : i < ell) (hstep : StepData T i R)
    (hv : ∀ j, v ∉ T j) :
    ∀ j, j < ell → 2 ^ j ≤ tierTotal (tierStepSucc T i R v) j := by
  intro j hjell
  have htot := stepSucc_total hstep h.hdisj hv j
  rw [htot]
  by_cases hji : j < i
  · rw [if_pos hji]
    have h2 : 2 ^ j ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (le_of_lt hji)
    have hR := hstep.card_ge
    omega
  · rw [if_neg hji]
    have hkj : k ≤ j := by omega
    have hcum := h.hcum j hkj hjell
    omega

/-- A valid failed update below the top tier preserves the cumulative bounds between k and ell
when a nonempty remainder stays in tier i [DurrEtAl2006]. -/
theorem tier_cumul_fail_leftover [DecidableEq V] {T : ℕ → Finset V} {k ell i : ℕ}
    {R : Finset V} (h : TierInv T k ell) (_hi : k ≤ i) (_hielt : i < ell)
    (hstep : StepData T i R) (hne : T i \ R ≠ ∅) :
    ∀ j, k ≤ j → j < ell → 2 ^ j ≤ tierTotal (tierStepFail T i R) j := by
  intro j hkj hjell
  have htot := stepFail_total hstep h.hdisj j
  rw [htot]
  by_cases hji : j = i
  · rw [hji, if_pos rfl]
    have hbig := (hstep.proper_card hne).1
    have hRc := (hstep.proper_card hne).2
    have hsingle : (T i).card ≤ tierTotal T i := by
      unfold tierTotal
      exact Finset.single_le_sum (f := fun l => (T l).card) (fun l _ => Nat.zero_le _)
        (Finset.mem_range.mpr (Nat.lt_succ_self i))
    have hpow : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [pow_succ]; ring
    omega
  · rw [if_neg hji]
    have hcum := h.hcum j hkj hjell
    omega

/-- A valid failed update below the top tier preserves the cumulative bounds between k and ell
away from index i [DurrEtAl2006]. -/
theorem tier_cumul_fail_inherit [DecidableEq V] {T : ℕ → Finset V} {k ell i : ℕ}
    {R : Finset V} (h : TierInv T k ell) (_hielt : i < ell)
    (hstep : StepData T i R) :
    ∀ j, k ≤ j → j ≠ i → j < ell → 2 ^ j ≤ tierTotal (tierStepFail T i R) j := by
  intro j hkj hji hjell
  have htot := stepFail_total hstep h.hdisj j
  rw [htot, if_neg hji]
  have hcum := h.hcum j hkj hjell
  omega

/-- A successful update strictly below the top tier preserves its power-of-two size lower bound
[DurrEtAl2006]. -/
theorem tier_top_succ [DecidableEq V] {T : ℕ → Finset V} {k ell i : ℕ} {R : Finset V}
    {v : V} (h : TierInv T k ell) (hielt : i < ell) :
    2 ^ (ell - 1) ≤ (tierStepSucc T i R v ell).card := by
  have hell0 : ell ≠ 0 := by omega
  have helli : ¬ ell = i := by omega
  rw [stepSucc_pos T i R v ell hell0, if_neg helli]
  exact h.card_top

/-- A valid failed update strictly below the top tier preserves its power-of-two size lower
bound [DurrEtAl2006]. -/
theorem tier_top_fail [DecidableEq V] {T : ℕ → Finset V} {k ell i : ℕ} {R : Finset V}
    (h : TierInv T k ell) (hielt : i < ell) (hstep : StepData T i R) :
    2 ^ (ell - 1) ≤ (tierStepFail T i R ell).card := by
  have helli : ¬ ell = i := by omega
  rw [stepFail_card hstep h.hdisj ell, if_neg helli]
  by_cases h1 : ell = i + 1
  · rw [if_pos h1]
    have hcast : (T (i + 1)).card = (T ell).card := by rw [h1]
    rw [hcast]
    exact le_trans h.card_top (Nat.le_add_right _ _)
  · rw [if_neg h1]
    exact h.card_top

/-- The family consisting of the singleton {v0} at tier zero and empty higher tiers satisfies
`TierInv` with both endpoints zero [DurrEtAl2006]. -/
theorem tierInv_initial [DecidableEq V] (v0 : V) :
    TierInv (fun j => if j = 0 then ({v0} : Finset V) else ∅) 0 0 := by
  refine ⟨le_rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨⟨v0, by simp⟩, fun j hj => by omega⟩
  · refine ⟨⟨v0, by simp⟩, fun j hj => ?_⟩
    simp [show j ≠ 0 by omega]
  · intro p q hpq
    by_cases hp : p = 0
    · subst hp
      have hq : q ≠ 0 := by omega
      simp [hq]
    · simp [hp]
  · intro j
    by_cases hj : j = 0
    · subst hj
      right
      simp
    · left
      simp [hj]
  · intro j _ hlt
    omega

/-- A nonnegative weighted sum of terms bounded above by 1/3 is at most 1/3 when the total
weight is at most one [DurrEtAl2006]. -/
theorem lemma16_failure_bound {ι : Type*} (s : Finset ι) (q p : ι → ℝ)
    (hq : ∀ i ∈ s, 0 ≤ q i) (hq1 : (∑ i ∈ s, q i) ≤ 1)
    (hp : ∀ i ∈ s, p i ≤ 1 / 3) :
    (∑ i ∈ s, q i * p i) ≤ 1 / 3 := by
  calc (∑ i ∈ s, q i * p i) ≤ ∑ i ∈ s, q i * (1 / 3) :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hp i hi) (hq i hi)
    _ = (∑ i ∈ s, q i) * (1 / 3) := by rw [Finset.sum_mul]
    _ ≤ 1 * (1 / 3) := mul_le_mul_of_nonneg_right hq1 (by norm_num)
    _ = 1 / 3 := by norm_num

/-- A nonnegative weighted sum of tier failure expressions is at most 1/3 when the total weight
is at most one [DurrEtAl2006]. -/
theorem lemma16_tier_failure (m : ℕ) (q : ℕ → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hq1 : (∑ i ∈ Finset.range m, q i) ≤ 1) :
    (∑ i ∈ Finset.range m, q i * tierFailure i) ≤ 1 / 3 :=
  lemma16_failure_bound (Finset.range m) q tierFailure
    (fun i _ => hq i) hq1 (fun i _ => tierFailure_le_third i)

/-- For r > 1, the sum of rʲ through j = i is at most r/(r − 1) times rⁱ [DurrEtAl2006]. -/
theorem geom_sum_range_le {r : ℝ} (hr : 1 < r) (i : ℕ) :
    (∑ j ∈ Finset.range (i + 1), r ^ j) ≤ (r / (r - 1)) * r ^ i := by
  have hr0 : (0 : ℝ) < r := lt_trans zero_lt_one hr
  have hden : (0 : ℝ) < r - 1 := by linarith
  have hgeom : (∑ j ∈ Finset.range (i + 1), r ^ j) = (r ^ (i + 1) - 1) / (r - 1) := by
    rw [geom_sum_eq (ne_of_gt hr)]
  rw [hgeom]
  have hpos : (0 : ℝ) < r ^ i := pow_pos hr0 i
  calc (r ^ (i + 1) - 1) / (r - 1) ≤ r ^ (i + 1) / (r - 1) := by
        rw [div_le_div_iff_of_pos_right hden]
        linarith [pow_pos hr0 (i + 1)]
    _ = (r / (r - 1)) * r ^ i := by
        field_simp
        ring

/-- Bounds the finite geometric sum with ratio 2^(3/4) by its final power times the factor
2^(3/4)/(2^(3/4) − 1) [DurrEtAl2006]. -/
theorem lemma17_per_tier_geom (i : ℕ) :
    (∑ j ∈ Finset.range (i + 1), (Real.rpow 2 ((3 : ℝ) / 4)) ^ j) ≤
      (Real.rpow 2 ((3 : ℝ) / 4) / (Real.rpow 2 ((3 : ℝ) / 4) - 1)) *
        (Real.rpow 2 ((3 : ℝ) / 4)) ^ i :=
  geom_sum_range_le (Real.one_lt_rpow (by norm_num) (by norm_num)) i

/-- For each n there is a positive constant uniformly bounding finite weighted tier costs by
that constant times √n when the nonnegative weights are at most (1/2)^(2ⁱ) [DurrEtAl2006]. -/
theorem lemma17_expected_cost (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (q : ℕ → ℝ), (∀ i, 0 ≤ q i) →
      (∀ i, q i ≤ (1 / 2 : ℝ) ^ (2 ^ i)) →
      (∑ i ∈ Finset.range m, q i * tierIterCost n i) ≤ C * Real.sqrt (n : ℝ) := by
  refine ⟨2, by norm_num, ?_⟩
  intro m q hq0 hq

  have htier : ∀ i, tierIterCost n i ≤ (2 : ℝ) ^ i * Real.sqrt (n : ℝ) := by
    intro i
    unfold tierIterCost
    exact mul_le_mul_of_nonneg_right (rpow_two_three_quarters_le i) (Real.sqrt_nonneg _)

  have hterm : ∀ i, q i * tierIterCost n i ≤ (1 / 2 : ℝ) ^ i * Real.sqrt (n : ℝ) := by
    intro i
    calc q i * tierIterCost n i
        ≤ q i * ((2 : ℝ) ^ i * Real.sqrt (n : ℝ)) :=
          mul_le_mul_of_nonneg_left (htier i) (hq0 i)
      _ ≤ (1 / 2 : ℝ) ^ (2 ^ i) * ((2 : ℝ) ^ i * Real.sqrt (n : ℝ)) :=
          mul_le_mul_of_nonneg_right (hq i) (by positivity)
      _ = ((1 / 2 : ℝ) ^ (2 ^ i) * (2 : ℝ) ^ i) * Real.sqrt (n : ℝ) := by ring
      _ ≤ (1 / 2 : ℝ) ^ i * Real.sqrt (n : ℝ) :=
          mul_le_mul_of_nonneg_right (half_pow_two_pow_mul_pow_two_le i) (Real.sqrt_nonneg _)
  calc (∑ i ∈ Finset.range m, q i * tierIterCost n i)
      ≤ ∑ i ∈ Finset.range m, (1 / 2 : ℝ) ^ i * Real.sqrt (n : ℝ) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = (∑ i ∈ Finset.range m, (1 / 2 : ℝ) ^ i) * Real.sqrt (n : ℝ) := by
        rw [Finset.sum_mul]
    _ ≤ 2 * Real.sqrt (n : ℝ) :=
        mul_le_mul_of_nonneg_right (geom_half_sum_le m) (Real.sqrt_nonneg _)

end Qatlib.Papers.QQueryGraph04.MainResults.StrongConnectivity
