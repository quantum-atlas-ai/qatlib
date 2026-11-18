/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.QPrograms.MeasureProg
public import Qatlib.Concepts.AdaptiveLedger.BranchLedger

@[expose] public section

/-!
# Query billing for measurement programs

This module attaches a query bill to every outcome history of a measurement program by reusing
the trajectory ledger of the public `Qatlib.Concepts.AdaptiveLedger.BranchLedger`: the bill of a
history is the `charge` accumulated from the empty history, where `cost` assigns an abstract
number of queries to every intermediate history. The bill is additive along trajectory
concatenation (`charge_append`), and a uniform per-history bound `B` yields the input-size
carried total bound `n * B` (`charge_le_length`). On top of the ledger sit the worst-case bill
`worstQ` — a computed supremum over all length-`n` trajectories, never an assumed constant —
and the expected bill `expQ`, the Born-weighted average of the trajectory bills.

Instantiation by a measured query profile: `cost` stays abstract here; a query-cost instance sets
`cost h := QueryCount` of the circuit word implementing the policy step at history `h`
(`Qatlib.Foundations.QueryWordCore.Circuit`). Under that instance `progQCostApp` mirrors
`queryCount_append`: trajectory-additive billing of oracle queries. Fixed execution length `n`,
no early stopping, and no loops, within the finite-program interface; every statement in this module
is a finite equality or inequality, with no asymptotic claim.
-/

set_option autoImplicit false

open Matrix
open scoped ComplexOrder
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.AdaptiveLedger.BranchLedger
open Qatlib.Concepts.QPrograms.MeasureProg

namespace Qatlib.Concepts.QPrograms.QueryBilling

variable {O : Type} [Fintype O] {D : ℕ}

/-- The query bill of an outcome history: the public branch-ledger charge accumulated from the
empty history. `cost` prices every intermediate history in abstract query units; the final
history itself is not charged. -/
def progQCost (cost : List O → ℕ) (os : List O) : ℕ :=
  charge cost [] os

omit [Fintype O] in
/-- Extending the empty history by one outcome bills the empty history and then continues
charging from the extended history. -/
theorem progQCostCons (cost : List O → ℕ) (o : O) (os : List O) :
    progQCost cost (o :: os) = cost [] + charge cost [o] os :=
  rfl

omit [Fintype O] in
/-- A two-step history from the empty history bills exactly the empty and one-step histories. -/
theorem progQCostTwo (cost : List O → ℕ) (a b : O) :
    progQCost cost [a, b] = cost [] + cost [a] :=
  rfl

omit [Fintype O] in
/-- The query bill of a concatenated trajectory is the bill of the first part plus the bill of
the second part charged from the first-part history, the trajectory additivity of the public
ledger. -/
theorem progQCostApp (cost : List O → ℕ) (xs ys : List O) :
    progQCost cost (xs ++ ys) = progQCost cost xs + charge cost xs ys := by
  rw [progQCost, charge_append cost [] xs ys, List.nil_append, ← progQCost]

/-- The worst-case query bill over all length-`n` trajectories: a computed supremum, not an
assumed budget. -/
def worstQ (cost : List O → ℕ) (n : ℕ) : ℕ :=
  Finset.univ.sup fun xs : Fin n → O => progQCost cost (List.ofFn xs)

/-- Every length-`n` trajectory bill is dominated by the worst-case bill. -/
theorem worstQGe (cost : List O → ℕ) (n : ℕ) (xs : Fin n → O) :
    progQCost cost (List.ofFn xs) ≤ worstQ cost n := by
  unfold worstQ
  exact Finset.le_sup
    (f := fun ys : Fin n → O => progQCost cost (List.ofFn ys)) (Finset.mem_univ xs)

/-- If every intermediate history bills at most `B`, the worst-case length-`n` bill is at most
`n * B`, the input-size-carried uniform bound of the public ledger. -/
theorem worstQLe (cost : List O → ℕ) (n : ℕ) (B : ℕ) (hB : ∀ h, cost h ≤ B) :
    worstQ cost n ≤ n * B := by
  refine Finset.sup_le fun xs _ => ?_
  have hlen : (List.ofFn xs).length = n := List.length_ofFn
  calc progQCost cost (List.ofFn xs)
      ≤ (List.ofFn xs).length * B := charge_le_length cost [] (List.ofFn xs) B hB
    _ = n * B := by rw [hlen]

/-- The expected query bill of a length-`n` execution of a measurement program: the Born
history-weighted average of the trajectory bills. -/
noncomputable def expQ (policy : List O → Instrument O D D) (ρ : Operator D)
    (cost : List O → ℕ) (n : ℕ) : ℝ :=
  ∑ xs : Fin n → O, histProb policy ρ n xs * (progQCost cost (List.ofFn xs) : ℝ)

/-- The expected query bill is nonnegative on positive semidefinite inputs, since every history
weight and every bill is nonnegative. -/
theorem expQNonneg (policy : List O → Instrument O D D) {ρ : Operator D}
    (hρ : ρ.PosSemidef) (cost : List O → ℕ) (n : ℕ) : 0 ≤ expQ policy ρ cost n := by
  refine Finset.sum_nonneg fun xs _ => mul_nonneg ?_ ?_
  · exact progProbNonneg policy hρ (List.ofFn xs)
  · exact_mod_cast Nat.zero_le _

/-- A zero-weight trajectory contributes exactly nothing to the expected query bill. -/
theorem expQTermZero (policy : List O → Instrument O D D) (ρ : Operator D)
    (cost : List O → ℕ) (n : ℕ) (xs : Fin n → O) (h : histProb policy ρ n xs = 0) :
    histProb policy ρ n xs * (progQCost cost (List.ofFn xs) : ℝ) = 0 := by
  rw [h, zero_mul]

/-- On a density input the expected query bill is at most the worst-case bill: every history
weight lies in `[0, 1]` and rescales its trajectory bill, and zero-weight trajectories
contribute nothing. -/
theorem expQLeWorst (policy : List O → Instrument O D D) {ρ : Operator D}
    (hρ : IsDensityOperator ρ) (cost : List O → ℕ) (n : ℕ) :
    expQ policy ρ cost n ≤ (worstQ cost n : ℝ) := by
  have hdom : ∀ xs : Fin n → O,
      histProb policy ρ n xs * (progQCost cost (List.ofFn xs) : ℝ)
        ≤ histProb policy ρ n xs * (worstQ cost n : ℝ) :=
    fun xs => mul_le_mul_of_nonneg_left
      (by exact_mod_cast worstQGe cost n xs) (progProbNonneg policy hρ.1 (List.ofFn xs))
  calc expQ policy ρ cost n
      = ∑ xs : Fin n → O,
          histProb policy ρ n xs * (progQCost cost (List.ofFn xs) : ℝ) := rfl
    _ ≤ ∑ xs : Fin n → O, histProb policy ρ n xs * (worstQ cost n : ℝ) :=
        Finset.sum_le_sum fun xs _ => hdom xs
    _ = (∑ xs : Fin n → O, histProb policy ρ n xs) * (worstQ cost n : ℝ) :=
        (Finset.sum_mul _ _ _).symm
    _ = 1 * (worstQ cost n : ℝ) := by rw [sumHistProbOne policy n hρ]
    _ = (worstQ cost n : ℝ) := one_mul _

end Qatlib.Concepts.QPrograms.QueryBilling
