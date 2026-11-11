/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ManyBodyFermi97.MainResults.Antisymmetrization
import Qatlib.Papers.ManyBodyFermi97.MainResults.SignedOrbit
import Mathlib.GroupTheory.Perm.Support

/-!
# Exchange signs and antisymmetrization cost schedules

This module formalizes exchange-parity identities associated with [AbramsLloyd1997]. A product
of swaps has phase (−1) to the number of swaps, giving the odd and even exchange phases and
independence from the chosen decomposition.

The cost statements bound the defined antisymmetrization step budgets. The circuit `schedule`
consists of repeated identity gates: its theorems verify the budgeted gate count, unitarity,
zero query count, and the doubled cost of appending its reverse.

## Main statements

* `parity_prod_swaps`: Exchange phase equals (−1) raised to the swap count.
* `schedule_correct`: The identity-gate schedule is unitary and uses no queries.
* `cleanup_doubles_cost`: Appending the reversed schedule doubles the cost.

## References

* [Abrams and Lloyd, 1997][AbramsLloyd1997]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ManyBodyFermi97.MainResults.ExchangeSign
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.CircuitReversal.ReversalAlgebra
open scoped Classical BigOperators

/-- The integer sign of a product of swaps equals (−1) raised to the list length. -/
theorem int_sign_prod_swaps {n : ℕ} (l : List (Equiv.Perm (Fin n)))
    (hl : ∀ g ∈ l, Equiv.Perm.IsSwap g) :
    (Equiv.Perm.sign l.prod : ℤ) = (-1 : ℤ) ^ l.length := by
  rw [Equiv.Perm.sign_prod_list_swap hl, Units.val_pow_eq_pow_val]
  simp

/-- The complex exchange parity of a product of swaps equals (−1) raised to the number of swaps
[AbramsLloyd1997]. -/
theorem parity_prod_swaps {n : ℕ} (l : List (Equiv.Perm (Fin n)))
    (hl : ∀ g ∈ l, Equiv.Perm.IsSwap g) :
    SignedOrbit.parity l.prod = (-1 : ℂ) ^ l.length := by
  unfold SignedOrbit.parity
  rw [int_sign_prod_swaps l hl]
  push_cast
  ring

/-- A product of an odd number of swaps has complex exchange phase −1 [AbramsLloyd1997]. -/
theorem odd_exchange_phase {n : ℕ} (l : List (Equiv.Perm (Fin n)))
    (hl : ∀ g ∈ l, Equiv.Perm.IsSwap g) (hodd : Odd l.length) :
    SignedOrbit.parity l.prod = -1 := by
  rw [parity_prod_swaps l hl]
  exact hodd.neg_one_pow

/-- A product of an even number of swaps has complex exchange phase 1 [AbramsLloyd1997]. -/
theorem even_exchange_phase {n : ℕ} (l : List (Equiv.Perm (Fin n)))
    (hl : ∀ g ∈ l, Equiv.Perm.IsSwap g) (heven : Even l.length) :
    SignedOrbit.parity l.prod = 1 := by
  rw [parity_prod_swaps l hl]
  exact heven.neg_one_pow

/-- Lists with equal permutation products have equal complex exchange parities. -/
theorem exchange_phase_well_defined {n : ℕ} (l l' : List (Equiv.Perm (Fin n)))
    (hperm : l.prod = l'.prod) :
    SignedOrbit.parity l.prod = SignedOrbit.parity l'.prod := by
  rw [hperm]

/-- The permutation index for n particles has n! elements [AbramsLloyd1997]. -/
theorem orbit_branch_count (n : ℕ) :
    Fintype.card (Equiv.Perm (Fin n)) = n.factorial :=
  antisym_state_count n

/-- For n, q ≥ 1, the step-two cost model is at most n²q² [AbramsLloyd1997]. -/
theorem antisym_step_two_le {n q : ℕ} (hn : 1 ≤ n) (hq : 1 ≤ q) :
    antisymStepTwoCost n q ≤ n ^ 2 * q ^ 2 := by
  unfold antisymStepTwoCost
  exact Nat.mul_le_mul_right _ (sq_ge_self hn)

/-- For q ≥ 1, the step-three cost model is at most n²q² [AbramsLloyd1997]. -/
theorem antisym_step_three_le {n q : ℕ} (hq : 1 ≤ q) :
    antisymStepThreeCost n q ≤ n ^ 2 * q ^ 2 := by
  unfold antisymStepThreeCost
  exact Nat.mul_le_mul_left _ (sq_ge_self hq)

/-- For n, q ≥ 1, the step-four cost model is at most 2n²q² [AbramsLloyd1997]. -/
theorem antisym_step_four_le {n q : ℕ} (hn : 1 ≤ n) (hq : 1 ≤ q) :
    antisymStepFourCost n ≤ 2 * n ^ 2 * q ^ 2 := by
  unfold antisymStepFourCost
  have hn2 : n ≤ n ^ 2 := sq_ge_self hn
  have hq2pos : 1 ≤ q ^ 2 := by
    calc 1 = 1 * 1 := by ring
      _ ≤ q * q := Nat.mul_le_mul hq hq
      _ = q ^ 2 := by ring
  have hclog : Nat.clog 2 n ≤ n := quWordBits_le n
  have ha : n * Nat.clog 2 n ≤ n * n := Nat.mul_le_mul_left n hclog
  calc 2 * n * Nat.clog 2 n = 2 * (n * Nat.clog 2 n) := by ring
    _ ≤ 2 * (n * n) := Nat.mul_le_mul_left 2 ha
    _ = 2 * n ^ 2 := by ring
    _ = 2 * n ^ 2 * 1 := by ring
    _ ≤ 2 * n ^ 2 * q ^ 2 := Nat.mul_le_mul_left _ hq2pos

/-- The total antisymmetrization cost is the sum of the three defined step-cost expressions
[AbramsLloyd1997]. -/
theorem four_step_decomposition (n q : ℕ) :
    antisymTotalCost n q =
      antisymStepTwoCost n q + antisymStepThreeCost n q + antisymStepFourCost n := rfl

/-- A circuit of identity gates whose length is the modeled total antisymmetrization cost. -/
def schedule (I : Type*) [Fintype I] [DecidableEq I] (n q : ℕ) : Circuit I :=
  List.replicate (antisymTotalCost n q) (Step.gate (1 : Matrix I I ℂ))

/-- The identity-gate schedule has gate count `antisymTotalCost n q`. -/
theorem schedule_gateCount {I : Type*} [Fintype I] [DecidableEq I] (n q : ℕ) :
    GateCount (schedule I n q) = antisymTotalCost n q := by
  unfold schedule
  induction antisymTotalCost n q with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

/-- The identity-gate schedule is a unitary circuit with zero oracle queries [AbramsLloyd1997]. -/
theorem schedule_correct {I : Type*} [Fintype I] [DecidableEq I] (n q : ℕ) :
    IsUnitaryCircuit (schedule I n q) ∧ QueryCount (schedule I n q) = 0 := by
  unfold schedule
  induction antisymTotalCost n q with
  | zero => simp
  | succ k ih =>
    simp only [List.replicate_succ, isUnitaryCircuit_gate, queryCount_gate]
    exact ⟨⟨by simp, ih.1⟩, ih.2⟩

/-- Appending the reverse of the identity-gate schedule gives gate count twice `antisymTotalCost
n q` [AbramsLloyd1997]. -/
theorem cleanup_doubles_cost {I : Type*} [Fintype I] [DecidableEq I] (n q : ℕ) :
    GateCount (schedule I n q ++ ReverseCircuit (schedule I n q)) =
      2 * antisymTotalCost n q := by
  rw [gateCount_append, gateCount_reverseCircuit, schedule_gateCount]
  ring
end Qatlib.Papers.ManyBodyFermi97.MainResults.ExchangeSign
