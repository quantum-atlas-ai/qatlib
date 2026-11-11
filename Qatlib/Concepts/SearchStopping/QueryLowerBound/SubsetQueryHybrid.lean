/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.QueryLowerBound.FixedQueryLowerBound
import Mathlib.Data.Finset.Powerset

/-!
# Subset incidence bounds for query hybrids

Defines `MarkedSubsets` and the coordinate query set `SubsetQuerySet` associated with a marked
subset of labels. Binomial counting identities give incidence and overlap budgets, and
`subset_query_mass` bounds the total projected mass across all subsets of a fixed cardinality.
For the quantum-search analysis, see [BoyerEtAl1998].

## Main statements

* `markedSubsets_incidence`: For positive `t`, each label belongs to exactly `(Fintype.card Y -
  1).choose (t - 1)` subsets of cardinality `t`, expressed as a real-valued incidence sum.
* `subset_overlap_budget`: For `0 < t ≤ N`, natural division gives `(N / t) * (N - 1).choose (t
  - 1) ≤ N.choose t`.
* `subset_query_mass`: For positive `t`, the summed squared projection mass over all `t`-element
  marked subsets is at most the subset-incidence count times `‖ψ‖ ^ 2`.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Concepts.SearchStopping.QueryLowerBound

open scoped BigOperators

/-- The finite type of subsets of `Y` having cardinality `t`. -/
abbrev MarkedSubsets (Y : Type*) [Fintype Y] (t : ℕ) :=
  ↥((Finset.univ : Finset Y).powersetCard t)

/-- The finite set of coordinates whose optional label is a member of the marked label set `A`. -/
noncomputable def SubsetQuerySet {C Y : Type*} [Fintype C] [DecidableEq Y]
    (label : C → Option Y) (A : Finset Y) : Finset C := by
  classical
  exact Finset.univ.filter (fun c => match label c with
    | none => False
    | some y => y ∈ A)

/-- The number of `t`-element subsets of a finite type `Y` is `(Fintype.card Y).choose t`. -/
theorem markedSubsets_card (Y : Type*) [Fintype Y] (t : ℕ) :
    Fintype.card (MarkedSubsets Y t) = (Fintype.card Y).choose t := by
  simp [MarkedSubsets]

/-- For positive `t`, each label belongs to exactly `(Fintype.card Y - 1).choose (t - 1)`
subsets of cardinality `t`, expressed as a real-valued incidence sum. -/
theorem markedSubsets_incidence {Y : Type*} [Fintype Y] [DecidableEq Y]
    (t : ℕ) (ht : 0 < t) (y : Y) :
    (∑ A : MarkedSubsets Y t, if y ∈ A.val then (1 : ℝ) else 0) =
      (((Fintype.card Y - 1).choose (t - 1) : ℕ) : ℝ) := by
  change (∑ A : ↥((Finset.univ : Finset Y).powersetCard t),
    if y ∈ A.val then (1 : ℝ) else 0) = _
  rw [Finset.sum_coe_sort _ (fun A : Finset Y => if y ∈ A then (1 : ℝ) else 0),
    ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  have h := Finset.card_filter_powersetCard_subset ({y} : Finset Y) Finset.univ t
    (by simp) (by simpa using! ht)
  exact_mod_cast (show ((Finset.univ.powersetCard t).filter (fun A : Finset Y => y ∈ A)).card =
    (Fintype.card Y - 1).choose (t - 1) from by simpa using h)

/-- For `0 < t ≤ N`, natural division gives `(N / t) * (N - 1).choose (t - 1) ≤ N.choose t`. -/
theorem subset_overlap_budget (N t : ℕ) (ht : 0 < t) (htN : t ≤ N) :
    (N / t) * (N - 1).choose (t - 1) ≤ N.choose t := by
  have hN : 1 ≤ N := by omega
  have ht1 : 1 ≤ t := by omega
  have hchoose := Nat.add_one_mul_choose_eq (N - 1) (t - 1)
  rw [Nat.sub_add_cancel hN, Nat.sub_add_cancel ht1] at hchoose
  have hraw := Nat.mul_le_mul_right ((N - 1).choose (t - 1)) (Nat.div_mul_le_self N t)
  rw [hchoose] at hraw
  apply Nat.le_of_mul_le_mul_left (c := t) _ ht
  nlinarith only [hraw]

/-- For positive `t`, the summed squared projection mass over all `t`-element marked subsets is
at most the subset-incidence count times `‖ψ‖ ^ 2`. -/
theorem subset_query_mass {C Y : Type*} [Fintype C] [DecidableEq C]
    [Fintype Y] [DecidableEq Y] (t : ℕ) (ht : 0 < t)
    (label : C → Option Y) (ψ : EuclideanSpace ℂ C) :
    (∑ A : MarkedSubsets Y t, ‖QueryProjection (SubsetQuerySet label A.val) ψ‖ ^ 2) ≤
      (((Fintype.card Y - 1).choose (t - 1) : ℕ) : ℝ) * ‖ψ‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  cases hf : label c with
  | none =>
    simpa [QueryProjection, SubsetQuerySet, hf] using
      (mul_nonneg (Nat.cast_nonneg ((Fintype.card Y - 1).choose (t - 1)) : (0 : ℝ) ≤ _)
        (sq_nonneg ‖ψ c‖))
  | some y =>
    have hterm (A : MarkedSubsets Y t) :
        ‖QueryProjection (SubsetQuerySet label A.val) ψ c‖ ^ 2 =
          (if y ∈ A.val then (1 : ℝ) else 0) * ‖ψ c‖ ^ 2 := by
      by_cases hy : y ∈ A.val <;> simp [QueryProjection, SubsetQuerySet, hf, hy]
    simp_rw [hterm]
    rw [← Finset.sum_mul, markedSubsets_incidence t ht y]

end Qatlib.Concepts.SearchStopping.QueryLowerBound
