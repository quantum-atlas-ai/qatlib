/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.AdaptiveHistoryDefs

/-!
# Composition and bounds for adaptive branch ledgers

This module proves concatenation laws for adaptive branch maps and their accumulated charges.
`charge_le_length` bounds the total charge by the path length times a uniform per-history bound,
and `g1` combines the ledger laws. For background, see [Watrous2018].

## Main statements

* `branch_append`: The branch map for concatenated outcome lists is the composition of the first
  branch map and the second branch map started from the extended history.
* `charge_append`: The charge of concatenated outcome lists is the first charge plus the second
  charge started from the extended history.
* `charge_le_length`: If every history has cost at most `B`, the charge along `xs` is at most
  `xs.length * B`.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.AdaptiveLedger.BranchLedger
open Qatlib

variable {O : Type} [Fintype O] [DecidableEq O] {D : ℕ}

omit [DecidableEq O] in

/-- The branch map for concatenated outcome lists is the composition of the first branch map and
the second branch map started from the extended history. -/
lemma branch_append (policy : List O → Instrument O D D) (h xs ys : List O) :
    branch policy h (xs ++ ys) =
      (branch policy (h ++ xs) ys).comp (branch policy h xs) := by
  induction xs generalizing h with
  | nil =>
    simp [branch]
  | cons o xs ih =>
    simp only [List.cons_append, branch]
    rw [ih (h ++ [o]), List.append_assoc, List.singleton_append]
    simp [LinearMap.comp_assoc]

omit [Fintype O] [DecidableEq O] in

/-- The charge of concatenated outcome lists is the first charge plus the second charge started
from the extended history. -/
lemma charge_append (cost : List O → ℕ) (h xs ys : List O) :
    charge cost h (xs ++ ys) = charge cost h xs + charge cost (h ++ xs) ys := by
  induction xs generalizing h with
  | nil =>
    simp [charge]
  | cons o xs ih =>
    simp only [List.cons_append, charge]
    rw [ih (h ++ [o]), List.append_assoc, List.singleton_append]
    omega

omit [Fintype O] [DecidableEq O] in

/-- If every history has cost at most `B`, the charge along `xs` is at most `xs.length * B`. -/
lemma charge_le_length (cost : List O → ℕ) (h xs : List O)
    (B : ℕ) (hB : ∀ hist, cost hist ≤ B) :
    charge cost h xs ≤ xs.length * B := by
  induction xs generalizing h with
  | nil =>
    simp [charge]
  | cons o xs ih =>
    simp only [charge, List.length_cons]
    have hstep : cost h ≤ B := hB h
    have htail := ih (h ++ [o])
    calc
      cost h + charge cost (h ++ [o]) xs ≤ B + xs.length * B := Nat.add_le_add hstep htail
      _ = (xs.length + 1) * B := by
        rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-- Adaptive branch maps compose along concatenated histories, charges add along those
histories, and a uniform step-cost bound gives a length-times-bound total charge. -/
theorem g1 :
    ∀ (O : Type) [Fintype O] [DecidableEq O] (D : ℕ)
      (policy : List O → Instrument O D D) (cost : List O → ℕ)
      (h xs ys : List O),
      branch policy h (xs ++ ys) =
        (branch policy (h ++ xs) ys).comp (branch policy h xs) ∧
      charge cost h (xs ++ ys) = charge cost h xs + charge cost (h ++ xs) ys ∧
      (∀ B : ℕ, (∀ hist, cost hist ≤ B) → charge cost h xs ≤ xs.length * B) := by
  intro O _ _ D policy cost h xs ys
  exact ⟨branch_append policy h xs ys, charge_append cost h xs ys,
    fun B hB => charge_le_length cost h xs B hB⟩

end Qatlib.Concepts.AdaptiveLedger.BranchLedger
