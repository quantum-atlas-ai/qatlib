/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.GraphQuery.EdgeQuery.GraphCollision
public import Qatlib.Foundations.QueryWordCore.Circuit
public import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryMagnitude

@[expose] public section
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false

namespace Qatlib.Concepts.GraphQuery.GcBaselines

open Qatlib

inductive GadgetVertex (n : ℕ) where
  | station : GadgetVertex n
  | layer : Fin 4 → Fin n → GadgetVertex n
  deriving DecidableEq, Fintype

def gadgetVertexSumEquiv (n : ℕ) : GadgetVertex n ≃ (Unit ⊕ (Fin 4 × Fin n)) where
  toFun v := match v with
    | .station => Sum.inl ()
    | .layer ℓ j => Sum.inr (ℓ, j)
  invFun s := match s with
    | .inl _ => .station
    | .inr p => .layer p.1 p.2
  left_inv v := by cases v <;> rfl
  right_inv s := by cases s <;> rfl

/-- Computes the number of gadget vertices as four times `n` plus one. -/
lemma card_gadgetVertex (n : ℕ) : Fintype.card (GadgetVertex n) = 4 * n + 1 := by
  rw [Fintype.card_congr (gadgetVertexSumEquiv n), Fintype.card_sum]
  simp
  omega

def gcOr {n : ℕ} (adj : Fin n → Fin n → Bool) (x : Fin n → Fin n → Bool) : Bool :=
  decide (∃ u v : Fin n, adj u v = true ∧ (∃ a, x u a = true) ∧ (∃ a, x v a = true))

def gadgetAdjAt {n : ℕ} (adj : Fin n → Fin n → Bool) (x : Fin n → Fin n → Bool) :
    GadgetVertex n → GadgetVertex n → Bool
  | .station, .layer 0 _ => true
  | .layer 0 _, .station => true
  | .station, .layer 3 _ => true
  | .layer 3 _, .station => true
  | .layer 1 j, .layer 2 k => adj j k
  | .layer 2 k, .layer 1 j => adj j k
  | .layer 0 a, .layer 1 b => x b a
  | .layer 1 b, .layer 0 a => x b a
  | .layer 2 b, .layer 3 a => x b a
  | .layer 3 a, .layer 2 b => x b a
  | _, _ => false

def cycle5ThroughStation {n : ℕ} (A : GadgetVertex n → GadgetVertex n → Bool) : Bool :=
  decide (∃ v1 v2 v3 v4 : GadgetVertex n,
    v1 ≠ .station ∧ v2 ≠ .station ∧ v3 ≠ .station ∧ v4 ≠ .station ∧
      v1 ≠ v2 ∧ v1 ≠ v3 ∧ v1 ≠ v4 ∧ v2 ≠ v3 ∧ v2 ≠ v4 ∧ v3 ≠ v4 ∧
      A .station v1 = true ∧ A v1 v2 = true ∧ A v2 v3 = true ∧ A v3 v4 = true ∧
      A v4 .station = true)

def matchingAdj (n : ℕ) : Fin n → Fin n → Bool := fun u v =>
  decide (u.val % 2 = 0 ∧ u.val + 1 = v.val) ||
    decide (v.val % 2 = 0 ∧ v.val + 1 = u.val)

def matchingEdges (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun e => decide (e.1.val % 2 = 0 ∧ e.1.val + 1 = e.2.val)

def gadgetAddrCount (n : ℕ) : ℕ := (4 * n + 1) * (4 * n + 1)

noncomputable def gadgetAddrEquiv (n : ℕ) :
    Fin (gadgetAddrCount n) ≃ (GadgetVertex n × GadgetVertex n) :=
  (Fintype.equivFinOfCardEq (by
    simp only [gadgetAddrCount, Fintype.card_prod, card_gadgetVertex])).symm

noncomputable def gadgetOracleBit {n : ℕ} (adj : Fin n → Fin n → Bool) (x : Fin n → Fin n → Bool) :
    Fin (gadgetAddrCount n) → Bool := fun i =>
  gadgetAdjAt adj x (gadgetAddrEquiv n i).1 (gadgetAddrEquiv n i).2

def GadgetSimpleAdj (n : ℕ) : Type :=
  { A : GadgetVertex n → GadgetVertex n → Bool // ∀ p q, A p q = A q p ∧ A p p = false }

instance {n : ℕ} : Fintype (GadgetSimpleAdj n) := Subtype.fintype _

noncomputable def gadgetOracleInput {n : ℕ} (S : GadgetSimpleAdj n) :
    Fin (gadgetAddrCount n) → Bool := fun i =>
  S.1 (gadgetAddrEquiv n i).1 (gadgetAddrEquiv n i).2

end Qatlib.Concepts.GraphQuery.GcBaselines

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator
namespace Qatlib.Concepts.GraphQuery.GcBaselines.QuantumAlgorithmsForPathAndCycleContainmentProblems2026

/-- Shows that gadget adjacency is symmetric and has no self-loops. -/
theorem gadgetAdjAt_simple {n : ℕ} (adj : Fin n → Fin n → Bool) (x : Fin n → Fin n → Bool) :
    ∀ p q, gadgetAdjAt adj x p q = gadgetAdjAt adj x q p ∧ gadgetAdjAt adj x p p = false := by
  intro p q
  constructor
  · cases p with
    | station =>
      cases q with
      | station => rfl
      | layer l a => fin_cases l <;> rfl
    | layer l a =>
      cases q with
      | station => fin_cases l <;> rfl
      | layer k b => fin_cases l <;> fin_cases k <;> rfl
  · cases p with
    | station => rfl
    | layer l a => fin_cases l <;> rfl
end Qatlib.Concepts.GraphQuery.GcBaselines.QuantumAlgorithmsForPathAndCycleContainmentProblems2026
