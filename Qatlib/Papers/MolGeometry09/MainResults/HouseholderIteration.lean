/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MolGeometry09.MainResults.NewtonIteration
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

namespace Qatlib.Papers.MolGeometry09.MainResults.HouseholderIteration

open Qatlib.Papers.MolGeometry09.MainResults.DerivativeQueryLedger
open Qatlib.Papers.MolGeometry09.MainResults.NewtonIteration
open Qatlib.Concepts.SignalPrimitive.GridGradient
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open scoped BigOperators

def householderCircuit (d M : ℕ) : ℕ → Circuit (GradientGrid d M)
  | 0 => derivativeCircuit d M 1
  | l + 1 => householderCircuit d M l ++ derivativeCircuit d M (l + 2)

@[simp] theorem householderCircuit_zero (d M : ℕ) :
    householderCircuit d M 0 = derivativeCircuit d M 1 := rfl

theorem householderCircuit_succ (d M l : ℕ) :
    householderCircuit d M (l + 1) =
      householderCircuit d M l ++ derivativeCircuit d M (l + 2) := rfl

def householderIterationQueries (d M l : ℕ) : ℕ :=
  ∑ m ∈ Finset.range (l + 1), higherDerivativeQueryLedger d M (m + 1)

theorem householderCircuit_queryCount (d M : ℕ) (hM : 0 < M) :
    ∀ l : ℕ, QueryCount (householderCircuit d M l) =
      ∑ m ∈ Finset.range (l + 1), QueryCount (derivativeCircuit d M (m + 1))
  | 0 => by
      simp
  | l + 1 => by
      have ih := householderCircuit_queryCount d M hM l
      rw [householderCircuit_succ, queryCount_append, ih]
      conv_rhs => rw [Finset.sum_range_succ]

theorem householderIterationQueries_eq_circuit (d M l : ℕ) (hM : 0 < M) :
    householderIterationQueries d M l = QueryCount (householderCircuit d M l) := by
  rw [householderCircuit_queryCount d M hM l]
  simp only [householderIterationQueries, higherDerivativeQueryLedger]

theorem sum_range_pow_two (l : ℕ) :
    ∑ m ∈ Finset.range (l + 1), 2 ^ m = 2 ^ (l + 1) - 1 := by
  induction l with
  | zero => simp
  | succ l ih =>
      rw [Finset.sum_range_succ, ih]
      have h : 2 ^ (l + 1 + 1) = 2 ^ (l + 1) + 2 ^ (l + 1) := by
        rw [pow_succ, Nat.mul_two]
      rw [h]
      have hpos : 1 ≤ 2 ^ (l + 1) := Nat.one_le_pow (l + 1) 2 (by norm_num)
      exact (Nat.sub_add_comm hpos).symm

theorem householder_ledger_eq_pow (d M l : ℕ) (hM : 0 < M) :
    householderIterationQueries d M l =
      ∑ m ∈ Finset.range (l + 1), 2 ^ m := by
  unfold householderIterationQueries
  apply Finset.sum_congr rfl
  intro m _
  rw [nth_derivative_query_count d M (m + 1) hM (Nat.succ_le_succ (Nat.zero_le m))]
  simp

theorem householder_query_count (d M l : ℕ) (hM : 0 < M) :
    householderIterationQueries d M l = 2 ^ (l + 1) - 1 := by
  rw [householder_ledger_eq_pow d M l hM, sum_range_pow_two l]

theorem householderCircuit_query_count (d M l : ℕ) (hM : 0 < M) :
    QueryCount (householderCircuit d M l) = 2 ^ (l + 1) - 1 := by
  rw [← householderIterationQueries_eq_circuit d M l hM, householder_query_count d M l hM]

theorem householder_order_one_eq_newton_circuit (d M : ℕ) (hM : 0 < M) :
    householderCircuit d M 1 = newtonCircuit d M := by
  rw [householderCircuit_succ, householderCircuit_zero, newtonCircuit_eq_gradient_hessian]

theorem householder_order_one_eq_newton (d M : ℕ) (hM : 0 < M) :
    householderIterationQueries d M 1 = 3 ∧
      householderIterationQueries d M 1 = newtonIterationQueries d M := by
  constructor
  · rw [householder_query_count d M 1 hM]
    norm_num
  · rw [householder_query_count d M 1 hM, (newton_iteration_three_queries d M hM).2.2]
    norm_num

theorem householderCircuit_unitary (d M : ℕ) (hM : 0 < M) :
    ∀ l : ℕ, IsUnitaryCircuit (householderCircuit d M l)
  | 0 => by
      rw [householderCircuit_zero]
      exact derivativeCircuit_unitary d M hM 1
  | l + 1 => by
      rw [householderCircuit_succ, isUnitaryCircuit_append]
      exact ⟨householderCircuit_unitary d M hM l, derivativeCircuit_unitary d M hM (l + 2)⟩

theorem householderCircuit_normalized_run (d M l : ℕ) (hM : 0 < M)
    (O : Matrix (GradientGrid d M) (GradientGrid d M) ℂ)
    (hO : O ∈ Matrix.unitaryGroup (GradientGrid d M) ℂ)
    {ψ : QState (GradientGrid d M)} (hψ : Normalized ψ) :
    Normalized (Run O (householderCircuit d M l) ψ) :=
  (householderCircuit_unitary d M hM l).normalized_run hO hψ

theorem householder_query_count_dimension_free
    (d d' M M' l : ℕ) (hM : 0 < M) (hM' : 0 < M') :
    householderIterationQueries d M l = householderIterationQueries d' M' l := by
  rw [householder_query_count d M l hM, householder_query_count d' M' l hM']

end Qatlib.Papers.MolGeometry09.MainResults.HouseholderIteration
