/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-!
# Counting the low-weight assignments read by reconstruction

The discussion after Theorem 2 uses assignments with at most three
ones. Grouping the subsets of variables by their cardinality counts
the distinct inputs. Every subset read in a low-weight Möbius
coefficient is again one of those inputs.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.AdiabPower02.MainResults

/-- The set of assignments whose support has size at most three. -/
def lowWeightAssignments (n : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.powerset.filter (fun S => S.card ≤ 3)

/-- The exact number of distinct low-weight inputs available to the
reconstruction in Section 6. -/
theorem card_lowWeightAssignments (n : ℕ) :
    (lowWeightAssignments n).card = 1 + n + n.choose 2 + n.choose 3 := by
  have h := Finset.sum_card_fiberwise_eq_card_filter
    ((Finset.univ : Finset (Fin n)).powerset) (Finset.range 4) Finset.card
  simp only [Finset.mem_range, Nat.lt_succ_iff, ← Finset.powersetCard_eq_filter,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at h
  change (∑ j ∈ Finset.range 4, n.choose j) = (lowWeightAssignments n).card at h
  rw [← h]
  simp [Finset.sum_range_succ]

/-- The subsets needed when computing a low-weight Möbius coefficient
can all be read from the same set of assignments. -/
theorem low_weight_queries_closed {n : ℕ} {S T : Finset (Fin n)}
    (hS : S ∈ lowWeightAssignments n) (hT : T ∈ S.powerset) :
    T ∈ lowWeightAssignments n := by
  simp only [lowWeightAssignments, Finset.mem_filter, Finset.mem_powerset,
    Finset.subset_univ, true_and] at hS ⊢
  exact (Finset.card_le_card (Finset.mem_powerset.1 hT)).trans hS

end Qatlib.Papers.AdiabPower02.MainResults
