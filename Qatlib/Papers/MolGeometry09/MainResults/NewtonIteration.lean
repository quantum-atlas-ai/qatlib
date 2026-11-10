/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MolGeometry09.MainResults.DerivativeQueryLedger
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.NormNum
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

namespace Qatlib.Papers.MolGeometry09.MainResults.NewtonIteration

open Qatlib.Papers.MolGeometry09.MainResults.DerivativeQueryLedger
open Qatlib.Concepts.SignalPrimitive.GridGradient
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit

def newtonCircuit (d M : ℕ) : Circuit (GradientGrid d M) :=
  derivativeCircuit d M 1 ++ derivativeCircuit d M 2

theorem newtonCircuit_eq_gradient_hessian (d M : ℕ) :
    newtonCircuit d M = derivativeCircuit d M 1 ++ derivativeCircuit d M 2 := rfl

def newtonIterationQueries (d M : ℕ) : ℕ := QueryCount (newtonCircuit d M)

theorem gradient_order_one (d M : ℕ) (hM : 0 < M) :
    higherDerivativeQueryLedger d M 1 = 1 := by
  simpa using! nth_derivative_query_count d M 1 hM le_rfl

theorem hessian_order_two (d M : ℕ) (hM : 0 < M) :
    higherDerivativeQueryLedger d M 2 = 2 := by
  simpa using! nth_derivative_query_count d M 2 hM (by norm_num)

theorem newton_iteration_three_queries (d M : ℕ) (hM : 0 < M) :
    higherDerivativeQueryLedger d M 1 = 1 ∧
      higherDerivativeQueryLedger d M 2 = 2 ∧
      newtonIterationQueries d M = 3 := by
  refine ⟨gradient_order_one d M hM, hessian_order_two d M hM, ?_⟩
  simp only [newtonIterationQueries, newtonCircuit_eq_gradient_hessian, queryCount_append,
    derivativeCircuit_one, gradient_base_energy_query d M hM, hessianCircuit_query_count d M hM]

theorem newtonCircuit_unitary (d M : ℕ) (hM : 0 < M) :
    IsUnitaryCircuit (newtonCircuit d M) := by
  rw [newtonCircuit_eq_gradient_hessian, isUnitaryCircuit_append]
  exact ⟨derivativeCircuit_unitary d M hM 1, derivativeCircuit_unitary d M hM 2⟩

theorem newtonCircuit_normalized_run (d M : ℕ) (hM : 0 < M)
    (O : Matrix (GradientGrid d M) (GradientGrid d M) ℂ)
    (hO : O ∈ Matrix.unitaryGroup (GradientGrid d M) ℂ)
    {ψ : QState (GradientGrid d M)} (hψ : Normalized ψ) :
    Normalized (Run O (newtonCircuit d M) ψ) :=
  (newtonCircuit_unitary d M hM).normalized_run hO hψ

theorem newton_iteration_queries_dimension_free
    (d d' M M' : ℕ) (hM : 0 < M) (hM' : 0 < M') :
    newtonIterationQueries d M = newtonIterationQueries d' M' := by
  rw [(newton_iteration_three_queries d M hM).2.2,
    (newton_iteration_three_queries d' M' hM').2.2]

theorem newton_hessian_output_size (d M : ℕ) (hM : 0 < M) :
    Fintype.card (Fin d × Fin d) = d ^ 2 ∧ newtonIterationQueries d M = 3 :=
  ⟨hessian_register_card d, (newton_iteration_three_queries d M hM).2.2⟩

theorem newton_beats_classical_finite_difference (d : ℕ) (hd : 2 ≤ d) :
    3 < d ^ 2 + 1 := by
  have h4 : 4 ≤ d ^ 2 := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ d ^ 2 := Nat.pow_le_pow_left hd 2
  exact Nat.lt_trans (by norm_num : 3 < 4) (Nat.lt_succ_of_le h4)

end Qatlib.Papers.MolGeometry09.MainResults.NewtonIteration
