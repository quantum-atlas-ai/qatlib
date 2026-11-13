/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MolGeometry09.MainResults.DerivativeQueryLedger
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.NormNum

/-!
# Newton circuit words and three-query ledgers

`newtonCircuit` concatenates the order-one and order-two derivative circuit words, corresponding
to the gradient and Hessian cost ledger in [KassalAspuruGuzik2009]. For positive grid size, the
two pieces have query counts one and two, giving total count three.

The module proves unitarity, preservation of normalization, dimension independence of the query
count, and arithmetic comparisons with the Hessian index-set size.

## Main statements

* `newton_iteration_three_queries`: The gradient and Hessian ledgers sum to a Newton count of
  three.
* `newtonCircuit_normalized_run`: The Newton word preserves normalization with a unitary oracle.
* `newton_hessian_output_size`: Combine the Hessian index count `d^2` with the query count
  three.

## References

* [Kassal and Aspuru-Guzik, 2009][KassalAspuruGuzik2009]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MolGeometry09.MainResults.NewtonIteration

open Qatlib.Papers.MolGeometry09.MainResults.DerivativeQueryLedger
open Qatlib.Concepts.SignalPrimitive.GridGradient
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit

/-- The concatenation of the order-one and order-two derivative circuit words. -/
def newtonCircuit (d M : ℕ) : Circuit (GradientGrid d M) :=
  derivativeCircuit d M 1 ++ derivativeCircuit d M 2

/-- The Newton circuit word is the gradient word followed by the order-two derivative word. -/
theorem newtonCircuit_eq_gradient_hessian (d M : ℕ) :
    newtonCircuit d M = derivativeCircuit d M 1 ++ derivativeCircuit d M 2 := rfl

/-- The oracle-query count of `newtonCircuit d M`. -/
def newtonIterationQueries (d M : ℕ) : ℕ := QueryCount (newtonCircuit d M)

/-- For positive grid size, the order-one derivative query ledger equals one. -/
theorem gradient_order_one (d M : ℕ) (hM : 0 < M) :
    higherDerivativeQueryLedger d M 1 = 1 := by
  simpa using! nth_derivative_query_count d M 1 hM le_rfl

/-- For positive grid size, the order-two derivative query ledger equals two. -/
theorem hessian_order_two (d M : ℕ) (hM : 0 < M) :
    higherDerivativeQueryLedger d M 2 = 2 := by
  simpa using! nth_derivative_query_count d M 2 hM (by norm_num)

/-- For positive grid size, the gradient ledger is one, the Hessian ledger is two, and the
Newton query count is three; see [KassalAspuruGuzik2009]. -/
theorem newton_iteration_three_queries (d M : ℕ) (hM : 0 < M) :
    higherDerivativeQueryLedger d M 1 = 1 ∧
      higherDerivativeQueryLedger d M 2 = 2 ∧
      newtonIterationQueries d M = 3 := by
  refine ⟨gradient_order_one d M hM, hessian_order_two d M hM, ?_⟩
  simp only [newtonIterationQueries, newtonCircuit_eq_gradient_hessian, queryCount_append,
    derivativeCircuit_one, gradient_base_energy_query d M hM, hessianCircuit_query_count d M hM]

/-- For positive grid size, the Newton circuit word satisfies `IsUnitaryCircuit`. -/
theorem newtonCircuit_unitary (d M : ℕ) (hM : 0 < M) :
    IsUnitaryCircuit (newtonCircuit d M) := by
  rw [newtonCircuit_eq_gradient_hessian, isUnitaryCircuit_append]
  exact ⟨derivativeCircuit_unitary d M hM 1, derivativeCircuit_unitary d M hM 2⟩

/-- Running the Newton circuit word with a unitary oracle preserves the normalization of the
input state; see [KassalAspuruGuzik2009]. -/
theorem newtonCircuit_normalized_run (d M : ℕ) (hM : 0 < M)
    (O : Matrix (GradientGrid d M) (GradientGrid d M) ℂ)
    (hO : O ∈ Matrix.unitaryGroup (GradientGrid d M) ℂ)
    {ψ : QState (GradientGrid d M)} (hψ : Normalized ψ) :
    Normalized (Run O (newtonCircuit d M) ψ) :=
  (newtonCircuit_unitary d M hM).normalized_run hO hψ

/-- The Newton query count is equal for any two dimensions and positive grid sizes; see
[KassalAspuruGuzik2009]. -/
theorem newton_iteration_queries_dimension_free
    (d d' M M' : ℕ) (hM : 0 < M) (hM' : 0 < M') :
    newtonIterationQueries d M = newtonIterationQueries d' M' := by
  rw [(newton_iteration_three_queries d M hM).2.2,
    (newton_iteration_three_queries d' M' hM').2.2]

/-- For positive grid size, the Hessian index set has `d^2` elements and the Newton circuit word
has three oracle queries; see [KassalAspuruGuzik2009]. -/
theorem newton_hessian_output_size (d M : ℕ) (hM : 0 < M) :
    Fintype.card (Fin d × Fin d) = d ^ 2 ∧ newtonIterationQueries d M = 3 :=
  ⟨hessian_register_card d, (newton_iteration_three_queries d M hM).2.2⟩

/-- For `d ≥ 2`, the modeled Newton count three is strictly less than `d^2 + 1`; see
[KassalAspuruGuzik2009]. -/
theorem newton_beats_classical_finite_difference (d : ℕ) (hd : 2 ≤ d) :
    3 < d ^ 2 + 1 := by
  have h4 : 4 ≤ d ^ 2 := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ d ^ 2 := Nat.pow_le_pow_left hd 2
  exact Nat.lt_trans (by norm_num : 3 < 4) (Nat.lt_succ_of_le h4)

end Qatlib.Papers.MolGeometry09.MainResults.NewtonIteration
