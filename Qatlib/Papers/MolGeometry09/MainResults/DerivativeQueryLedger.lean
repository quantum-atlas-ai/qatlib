/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SignalPrimitive.GridGradient.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Query ledgers for repeated gradient circuit words

`derivativeCircuit` starts with `gradientWord` at order one and doubles the preceding word at
each higher order. Its query ledger realizes the count `2^(n - 1)` for positive order and
positive grid size, matching the higher-derivative cost model discussed in
[KassalAspuruGuzik2009].

The module proves unitarity and preservation of normalization for these words, gives their gate
counts, and compares query counts with finite-difference arithmetic and register cardinalities.

## Main statements

* `derivativeCircuit_query_count`: The order-`n` word has `2^(n - 1)` queries under the stated
  positivity conditions.
* `derivativeCircuit_normalized_run`: Running the word with a unitary oracle preserves
  normalization.
* `hessian_array_size_vs_queries`: Pair the Hessian index count `d^2` with the word query count
  two.

## References

* [Kassal and Aspuru-Guzik, 2009][KassalAspuruGuzik2009]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

namespace Qatlib.Papers.MolGeometry09.MainResults.DerivativeQueryLedger

open Qatlib.Concepts.SignalPrimitive.GridGradient
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit

/-- A circuit-word family with empty order zero, `gradientWord` at order one, and two copies of
the preceding word at each subsequent order. -/
def derivativeCircuit (d M : ℕ) : ℕ → Circuit (GradientGrid d M)
  | 0 => []
  | 1 => gradientWord d M
  | n + 2 => derivativeCircuit d M (n + 1) ++ derivativeCircuit d M (n + 1)

/-- The order-zero derivative circuit word is empty. -/
@[simp] theorem derivativeCircuit_zero (d M : ℕ) : derivativeCircuit d M 0 = [] := rfl

/-- The order-one derivative circuit word is `gradientWord d M`. -/
@[simp] theorem derivativeCircuit_one (d M : ℕ) :
    derivativeCircuit d M 1 = gradientWord d M := rfl

/-- The order-`n + 2` word concatenates two copies of the order-`n + 1` word. -/
theorem derivativeCircuit_succ_succ (d M n : ℕ) :
    derivativeCircuit d M (n + 2) =
      derivativeCircuit d M (n + 1) ++ derivativeCircuit d M (n + 1) := rfl

/-- For positive grid size, `gradientWord d M` contains exactly one oracle query; see
[KassalAspuruGuzik2009]. -/
theorem gradient_base_energy_query (d M : ℕ) (hM : 0 < M) :
    QueryCount (gradientWord d M) = 1 :=
  (gradient_coordinate_qft_word_unitarity d M hM).2.1

/-- The oracle-query count of the circuit word `derivativeCircuit d M n`. -/
def higherDerivativeQueryLedger (d M n : ℕ) : ℕ := QueryCount (derivativeCircuit d M n)

/-- The query ledger doubles from order `n + 1` to order `n + 2`. -/
theorem higherDerivativeQueryLedger_succ_succ (d M n : ℕ) :
    higherDerivativeQueryLedger d M (n + 2) =
      2 * higherDerivativeQueryLedger d M (n + 1) := by
  unfold higherDerivativeQueryLedger
  rw [derivativeCircuit_succ_succ, queryCount_append]
  ring

/-- For positive grid size, the order-`k + 1` query ledger is `2^k` times the query count of the
base gradient word. -/
theorem higherDerivativeQueryLedger_closed_form (d M : ℕ) (hM : 0 < M) :
    ∀ k : ℕ, higherDerivativeQueryLedger d M (k + 1) =
      2 ^ k * QueryCount (gradientWord d M)
  | 0 => by
      rw [higherDerivativeQueryLedger, derivativeCircuit_one]
      simp
  | k + 1 => by
      have hrec : higherDerivativeQueryLedger d M (k + 1 + 1) =
          2 * higherDerivativeQueryLedger d M (k + 1) :=
        higherDerivativeQueryLedger_succ_succ d M k
      rw [hrec, higherDerivativeQueryLedger_closed_form d M hM k, pow_succ]
      ring

/-- For positive grid size and order `n ≥ 1`, the query ledger equals `2^(n - 1)`; see
[KassalAspuruGuzik2009]. -/
theorem nth_derivative_query_count (d M n : ℕ) (hM : 0 < M) (hn : 1 ≤ n) :
    higherDerivativeQueryLedger d M n = 2 ^ (n - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn)
  rw [higherDerivativeQueryLedger_closed_form d M hM k, gradient_base_energy_query d M hM,
    mul_one]
  simp

/-- For positive grid size and order `n ≥ 1`, the circuit word contains exactly `2^(n - 1)`
oracle queries; see [KassalAspuruGuzik2009]. -/
theorem derivativeCircuit_query_count (d M n : ℕ) (hM : 0 < M) (hn : 1 ≤ n) :
    QueryCount (derivativeCircuit d M n) = 2 ^ (n - 1) :=
  nth_derivative_query_count d M n hM hn

/-- For positive grid size, every derivative circuit word satisfies `IsUnitaryCircuit`. -/
theorem derivativeCircuit_unitary (d M : ℕ) (hM : 0 < M) :
    ∀ n : ℕ, IsUnitaryCircuit (derivativeCircuit d M n)
  | 0 => by
      rw [derivativeCircuit_zero]
      exact isUnitaryCircuit_nil
  | 1 => by
      rw [derivativeCircuit_one]
      exact (gradient_coordinate_qft_word_unitarity d M hM).1
  | n + 2 => by
      rw [derivativeCircuit_succ_succ, isUnitaryCircuit_append]
      exact ⟨derivativeCircuit_unitary d M hM (n + 1),
        derivativeCircuit_unitary d M hM (n + 1)⟩

/-- Running a derivative circuit word with a unitary oracle preserves the normalization of its
input state; see [KassalAspuruGuzik2009]. -/
theorem derivativeCircuit_normalized_run (d M n : ℕ) (hM : 0 < M)
    (O : Matrix (GradientGrid d M) (GradientGrid d M) ℂ)
    (hO : O ∈ Matrix.unitaryGroup (GradientGrid d M) ℂ)
    {ψ : QState (GradientGrid d M)} (hψ : Normalized ψ) :
    Normalized (Run O (derivativeCircuit d M n) ψ) :=
  (derivativeCircuit_unitary d M hM n).normalized_run hO hψ

/-- For positive grid size and order `n ≥ 1`, the gate count of the derivative circuit word is
`2^(n - 1) * (2 * d)`; see [KassalAspuruGuzik2009]. -/
theorem derivativeCircuit_gateCount (d M : ℕ) (hM : 0 < M) :
    ∀ n : ℕ, 1 ≤ n → GateCount (derivativeCircuit d M n) = 2 ^ (n - 1) * (2 * d)
  | 0, hn => by omega
  | 1, _ => by
      rw [derivativeCircuit_one, (gradient_coordinate_qft_word_unitarity d M hM).2.2]
      norm_num
  | n + 2, _ => by
      have ih := derivativeCircuit_gateCount d M hM (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n))
      rw [derivativeCircuit_succ_succ, gateCount_append, ih]
      simp only [Nat.add_sub_cancel]
      rw [show n + 2 - 1 = n + 1 by omega, pow_succ]
      ring

/-- At a fixed positive order, the query ledger is equal for any two dimensions and positive
grid sizes; see [KassalAspuruGuzik2009]. -/
theorem derivative_query_count_dimension_free
    (d d' M M' n : ℕ) (hM : 0 < M) (hM' : 0 < M') (hn : 1 ≤ n) :
    higherDerivativeQueryLedger d M n = higherDerivativeQueryLedger d' M' n := by
  rw [nth_derivative_query_count d M n hM hn,
    nth_derivative_query_count d' M' n hM' hn]

/-- For `d ≥ 2` and `n ≥ 1`, the modeled count `2^(n - 1)` is strictly less than `d^n + 1`; see
[KassalAspuruGuzik2009]. -/
theorem quantum_beats_classical_finite_difference
    (d n : ℕ) (hd : 2 ≤ d) (hn : 1 ≤ n) :
    2 ^ (n - 1) < d ^ n + 1 := by
  have h2n : 2 ^ n ≤ d ^ n := Nat.pow_le_pow_left hd n
  have hmono : 2 ^ (n - 1) ≤ 2 ^ n :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.sub_le n 1)
  exact Nat.lt_of_le_of_lt hmono (Nat.lt_succ_of_le h2n)

/-- The order-two circuit word consists of two consecutive gradient words. -/
theorem hessianCircuit_eq_two_gradient_calls (d M : ℕ) :
    derivativeCircuit d M 2 = gradientWord d M ++ gradientWord d M := rfl

/-- For positive grid size, the order-two circuit word contains exactly two oracle queries. -/
theorem hessianCircuit_query_count (d M : ℕ) (hM : 0 < M) :
    QueryCount (derivativeCircuit d M 2) = 2 := by
  rw [hessianCircuit_eq_two_gradient_calls, queryCount_append,
    gradient_base_energy_query d M hM]

/-- For positive grid size, the order-two circuit word has twice the oracle-query count of the
base gradient word. -/
theorem hessian_costs_twice_gradient (d M : ℕ) (hM : 0 < M) :
    QueryCount (derivativeCircuit d M 2) = 2 * QueryCount (gradientWord d M) := by
  rw [hessianCircuit_query_count d M hM, gradient_base_energy_query d M hM]

/-- The gradient grid `GradientGrid d M` has cardinality `M^d`. -/
theorem gradient_register_card (d M : ℕ) :
    Fintype.card (GradientGrid d M) = M ^ d := by
  simp [GradientGrid]

/-- The set of pairs of coordinate indices has cardinality `d^2`. -/
theorem hessian_register_card (d : ℕ) : Fintype.card (Fin d × Fin d) = d ^ 2 := by
  simp [pow_two]

/-- For positive grid size, the Hessian index set has `d^2` elements while the order-two circuit
word contains two oracle queries. -/
theorem hessian_array_size_vs_queries (d M : ℕ) (hM : 0 < M) :
    Fintype.card (Fin d × Fin d) = d ^ 2 ∧
      QueryCount (derivativeCircuit d M 2) = 2 :=
  ⟨hessian_register_card d, hessianCircuit_query_count d M hM⟩

end Qatlib.Papers.MolGeometry09.MainResults.DerivativeQueryLedger
