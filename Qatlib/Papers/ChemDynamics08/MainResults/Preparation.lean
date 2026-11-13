/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.LocalCapability

/-!
# Product state preparation

`LiftCircuitRight` extends a circuit to the second factor of a product register. It preserves
query and gate counts, preserves unitarity, and acts only on the second state when the oracle is
the identity. The preparation results combine two supplied preparation circuits with additive
gate cost.

These constructions support the treatment in [KassalEtAl2008].

## Main statements

* `product_state_preparation_cost`: constructs a query-free product preparation with exact
  additive gate count.
* `product_state_preparation_cost_le`: transfers upper bounds on the component gate counts.

## References

* [Kassal et al., 2008][KassalEtAl2008]
-/

set_option autoImplicit false

open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Papers.ChemDynamics08.MainResults.Preparation

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Lifts a circuit to the right tensor factor by tensoring each gate with the identity and
retaining each query step. -/
noncomputable def LiftCircuitRight (I J : Type*) [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] : Circuit J → Circuit (I × J)
  | [] => []
  | Step.gate V :: C =>
      Step.gate (TensorGate (1 : Matrix I I ℂ) V) :: LiftCircuitRight I J C
  | Step.query :: C => Step.query :: LiftCircuitRight I J C

/-- Lifting the empty circuit to the right tensor factor gives the empty circuit. -/
@[simp] theorem liftCircuitRight_nil (I J : Type*) [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] :
    LiftCircuitRight I J ([] : Circuit J) = [] := rfl

/-- Lifting a gate step tensors its gate with the identity on the left register. -/
@[simp] theorem liftCircuitRight_gate (I J : Type*) [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (V : Matrix J J ℂ) (C : Circuit J) :
    LiftCircuitRight I J (Step.gate V :: C)
      = Step.gate (TensorGate (1 : Matrix I I ℂ) V) :: LiftCircuitRight I J C := rfl

/-- Lifting a query step retains that step and lifts the remaining circuit. -/
@[simp] theorem liftCircuitRight_query (I J : Type*) [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (C : Circuit J) :
    LiftCircuitRight I J (Step.query :: C) = Step.query :: LiftCircuitRight I J C := rfl

/-- Lifting a circuit to the right tensor factor preserves its query count. -/
theorem queryCount_liftCircuitRight (I J : Type*) [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (C : Circuit J) :
    QueryCount (LiftCircuitRight I J C) = QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [ih]

/-- Lifting a circuit to the right tensor factor preserves its gate count. -/
theorem gateCount_liftCircuitRight (I J : Type*) [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (C : Circuit J) :
    GateCount (LiftCircuitRight I J C) = GateCount C := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [ih]

/-- Lifting a unitary circuit to the right tensor factor produces a unitary circuit. -/
theorem isUnitaryCircuit_liftCircuitRight (I J : Type*) [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] {C : Circuit J} (hC : IsUnitaryCircuit C) :
    IsUnitaryCircuit (LiftCircuitRight I J C) := by
  revert hC
  induction C with
  | nil => intro _; exact isUnitaryCircuit_nil
  | cons s C ih =>
    cases s with
    | gate V =>
      intro h
      obtain ⟨hV, hC⟩ := (isUnitaryCircuit_gate V C).mp h
      rw [liftCircuitRight_gate, isUnitaryCircuit_gate]
      exact ⟨tensorGate_unitary (Submonoid.one_mem _) hV, ih hC⟩
    | query =>
      intro h
      rw [liftCircuitRight_query, isUnitaryCircuit_query]
      exact ih ((isUnitaryCircuit_query C).mp h)

/-- With the identity oracle, the lifted circuit acts on the right factor of a tensor state and
leaves the left factor fixed. -/
theorem run_liftCircuitRight (I J : Type*) [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (C : Circuit J) (ψ : QState I) (χ : QState J) :
    Run 1 (LiftCircuitRight I J C) (TensorState ψ χ) = TensorState ψ (Run 1 C χ) := by
  induction C generalizing χ with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate V =>
      simp only [liftCircuitRight_gate, run_gate, applyGate_tensorGate, applyGate_one]
      exact ih _
    | query =>
      simp only [liftCircuitRight_query, run_query, applyGate_one]
      exact ih _

/-- Two supplied preparation circuits yield a unitary, query-free preparation of the tensor
state whose gate count is the sum of their gate counts [KassalEtAl2008]. -/
theorem product_state_preparation_cost
    (i₀ : I) (j₀ : J) (ψ : QState I) (φ : QState J)
    (hψ : HasPrepare ψ i₀) (hφ : HasPrepare φ j₀) :
    ∃ C : Circuit (I × J),
      IsUnitaryCircuit C ∧ QueryCount C = 0 ∧
      Run 1 C (Ket (i₀, j₀)) = TensorState ψ φ ∧
      GateCount C = GateCount hψ.prep + GateCount hφ.prep := by
  refine ⟨LiftCircuitTo J hψ.prep ++ LiftCircuitRight I J hφ.prep, ?_, ?_, ?_, ?_⟩
  · rw [isUnitaryCircuit_append]
    exact ⟨isUnitaryCircuit_liftCircuitTo hψ.unitary,
      isUnitaryCircuit_liftCircuitRight I J hφ.unitary⟩
  · rw [queryCount_append, queryCount_liftCircuitTo, queryCount_liftCircuitRight,
      hψ.query_free, hφ.query_free]
  · rw [run_append, ← tensorState_ket_ket i₀ j₀, run_liftCircuitTo, hψ.produces,
      run_liftCircuitRight, hφ.produces]
  · rw [gateCount_append, gateCount_liftCircuitTo, gateCount_liftCircuitRight]

/-- Component preparation bounds of `P` and `Q` yield a unitary, query-free product preparation
using at most `P + Q` gates [KassalEtAl2008]. -/
theorem product_state_preparation_cost_le
    (i₀ : I) (j₀ : J) (ψ : QState I) (φ : QState J)
    (hψ : HasPrepare ψ i₀) (hφ : HasPrepare φ j₀) (P Q : ℕ)
    (hP : GateCount hψ.prep ≤ P) (hQ : GateCount hφ.prep ≤ Q) :
    ∃ C : Circuit (I × J),
      IsUnitaryCircuit C ∧ QueryCount C = 0 ∧
      Run 1 C (Ket (i₀, j₀)) = TensorState ψ φ ∧ GateCount C ≤ P + Q := by
  obtain ⟨C, hC, hq, hr, hg⟩ := product_state_preparation_cost i₀ j₀ ψ φ hψ hφ
  exact ⟨C, hC, hq, hr, by rw [hg]; exact Nat.add_le_add hP hQ⟩

end Qatlib.Papers.ChemDynamics08.MainResults.Preparation
