/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.OracleAmplify.StandardOracleSequentialCopiesStat

/-!
# Routing sequential copies through one oracle

`StandardCopyCircuit` routes each query of one tensor factor through a shared bit-oracle
register. `StandardCopiesCircuit` concatenates these routed circuits, with exact query and gate
counts and a tensor-product execution formula. The background is described in [BennettEtAl1997].

## Main statements

* `standardCopyCircuit_run`: execution on one chosen tensor factor.
* `standardCopiesCircuit_spec`: unitarity, costs, and execution for all copies.

## References

* [Bennett et al., 1997][BennettEtAl1997]
-/

set_option autoImplicit false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.QueryComplexity.Amplification

namespace Qatlib.Concepts.UniformBqp.OracleAmplify
open Matrix
open scoped Classical BigOperators

variable {n k : ℕ} {W : Type} [Fintype W] [DecidableEq W]

/-- The permutation exchanging the shared oracle register with the oracle register of copy `j`,
while retaining that copy's workspace. -/
private def copySwap (j : Fin k)
    (z : (Fin n × Bool) × (Fin k → (Fin n × Bool) × W)) :=
  ((z.2 j).1, Function.update z.2 j (z.1, (z.2 j).2))

omit [Fintype W] [DecidableEq W] in

/-- Exchanging the shared oracle register with the register of copy `j` twice restores the full
configuration. -/
private theorem copySwap_involutive (j : Fin k) : Function.Involutive (copySwap (n := n) (W := W) j) := by
  intro z
  apply Prod.ext
  · simp [copySwap]
  · funext l
    by_cases hl : l = j
    · subst l; simp [copySwap]
    · simp [copySwap]

/-- The permutation matrix routing the oracle register of copy `j` to the shared query
interface. -/
private noncomputable def copySwapGate (j : Fin k) := permMatrix (copySwap (n := n) (W := W) j)

/-- The copy-routing permutation matrix is unitary. -/
private theorem copySwapGate_unitary (j : Fin k) :
    copySwapGate (n := n) (W := W) j ∈ Matrix.unitaryGroup _ ℂ :=
  permMatrix_unitary (copySwap_involutive j)

/-- Conjugating the shared workspace oracle by the routing gate applies the oracle to copy `j`
and leaves the shared state and other tensor factors unchanged. -/
private theorem routed_query (j : Fin k) (x : Fin n → Bool)
    (χ : QState (Fin n × Bool)) (ψ : Fin k → QState ((Fin n × Bool) × W)) :
    ApplyGate (copySwapGate j) (ApplyGate (workspaceBitOracle x)
      (ApplyGate (copySwapGate j) (TensorState χ (PiTensorState ψ)))) =
    TensorState χ (PiTensorState (Function.update ψ j
      (ApplyGate (workspaceBitOracle x) (ψ j)))) := by
  funext z
  simp only [copySwapGate, applyGate_permMatrix (copySwap_involutive j),
    applyGate_workspaceBitOracle, copySwap, Function.update_self, tensorState_apply,
    piTensorState_apply]
  congr 1
  apply Finset.prod_congr rfl
  intro l _
  by_cases hl : l = j
  · subst l
    simp [applyGate_workspaceBitOracle]
  · simp [hl]

/-- The circuit acting on copy `j`, lifting ordinary gates to that factor and routing each query
through the shared oracle register with two swaps. -/
noncomputable def StandardCopyCircuit (j : Fin k) :
    Circuit ((Fin n × Bool) × W) →
      Circuit ((Fin n × Bool) × (Fin k → (Fin n × Bool) × W))
  | [] => []
  | Step.gate U :: C => Step.gate (TensorGate 1 (FactorGate j U)) :: StandardCopyCircuit j C
  | Step.query :: C => Step.gate (copySwapGate j) :: Step.query ::
      Step.gate (copySwapGate j) :: StandardCopyCircuit j C

/-- Routing a unitary circuit to a selected copy preserves circuit unitarity. -/
theorem standardCopyCircuit_unitary (j : Fin k)
    {C : Circuit ((Fin n × Bool) × W)} (hC : IsUnitaryCircuit C) :
    IsUnitaryCircuit (StandardCopyCircuit j C) := by
  induction C with
  | nil => exact isUnitaryCircuit_nil
  | cons s C ih =>
    have htail : IsUnitaryCircuit C := fun U hU => hC U (List.mem_cons_of_mem _ hU)
    cases s with
    | gate U =>
      exact (isUnitaryCircuit_gate _ _).mpr
        ⟨tensorGate_unitary (Submonoid.one_mem _) (factorGate_unitary j (hC U List.mem_cons_self)),
          ih htail⟩
    | query =>
      exact (isUnitaryCircuit_gate _ _).mpr ⟨copySwapGate_unitary j,
        (isUnitaryCircuit_query _).mpr ((isUnitaryCircuit_gate _ _).mpr
          ⟨copySwapGate_unitary j, ih htail⟩)⟩

omit [Fintype W] in

/-- Routing a circuit to one copy preserves its query count. -/
theorem standardCopyCircuit_queries (j : Fin k) (C : Circuit ((Fin n × Bool) × W)) :
    QueryCount (StandardCopyCircuit j C) = QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [StandardCopyCircuit, QueryCount, ih]

omit [Fintype W] in

/-- Routing a circuit to one copy adds exactly two gates per oracle query to its gate count. -/
theorem standardCopyCircuit_gates (j : Fin k) (C : Circuit ((Fin n × Bool) × W)) :
    GateCount (StandardCopyCircuit j C) = GateCount C + 2 * QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [StandardCopyCircuit, GateCount, QueryCount, ih] <;> omega

/-- On a tensor input, the routed circuit runs the original circuit on copy `j` and preserves
the shared oracle state and other factors. -/
theorem standardCopyCircuit_run (j : Fin k) (C : Circuit ((Fin n × Bool) × W))
    (x : Fin n → Bool) (χ : QState (Fin n × Bool))
    (ψ : Fin k → QState ((Fin n × Bool) × W)) :
    Run (workspaceBitOracle x) (StandardCopyCircuit j C) (TensorState χ (PiTensorState ψ)) =
      TensorState χ (PiTensorState (Function.update ψ j (Run (workspaceBitOracle x) C (ψ j)))) := by
  induction C generalizing ψ with
  | nil => simp [StandardCopyCircuit, Run, Function.update_eq_self]
  | cons s C ih =>
    cases s with
    | gate U =>
      rw [StandardCopyCircuit, run_gate, applyGate_tensorGate, applyGate_one,
        applyGate_factorGate_piTensorState, ih, run_gate]
      simp
    | query =>
      rw [StandardCopyCircuit, run_gate, run_query, run_gate, routed_query, ih, run_query]
      simp

/-- The concatenation of the routed circuit over all `k` copies. -/
noncomputable def StandardCopiesCircuit (k : ℕ) (C : Circuit ((Fin n × Bool) × W)) :
    Circuit ((Fin n × Bool) × (Fin k → (Fin n × Bool) × W)) :=
  (List.finRange k).flatMap fun j => StandardCopyCircuit j C

/-- A concatenation of routed copies of a unitary circuit is unitary. -/
private theorem copies_list_unitary {C : Circuit ((Fin n × Bool) × W)}
    (hC : IsUnitaryCircuit C) (L : List (Fin k)) :
    IsUnitaryCircuit (L.flatMap fun j => StandardCopyCircuit j C) := by
  induction L with
  | nil => exact isUnitaryCircuit_nil
  | cons j L ih =>
    simp only [List.flatMap_cons, isUnitaryCircuit_append]
    exact ⟨standardCopyCircuit_unitary j hC, ih⟩

/-- The query count of a list of routed copies equals the list length times the original query
count. -/
private theorem copies_list_queries (C : Circuit ((Fin n × Bool) × W)) (L : List (Fin k)) :
    QueryCount (L.flatMap fun j => StandardCopyCircuit j C) = L.length * QueryCount C := by
  induction L with
  | nil => simp
  | cons j L ih => simp [queryCount_append, standardCopyCircuit_queries, ih, Nat.succ_mul, Nat.add_comm]

/-- The gate count of a list of routed copies is `L.length * (GateCount C + 2 * QueryCount C)`. -/
private theorem copies_list_gates (C : Circuit ((Fin n × Bool) × W)) (L : List (Fin k)) :
    GateCount (L.flatMap fun j => StandardCopyCircuit j C) =
      L.length * (GateCount C + 2 * QueryCount C) := by
  induction L with
  | nil => simp
  | cons j L ih => simp [gateCount_append, standardCopyCircuit_gates, ih, Nat.succ_mul, Nat.add_comm]

/-- On a tensor input, running routed copies indexed by a list without repetitions runs the
original circuit on exactly those factors and preserves the shared register. -/
private theorem copies_list_run (C : Circuit ((Fin n × Bool) × W)) (x : Fin n → Bool)
    (χ : QState (Fin n × Bool)) (L : List (Fin k)) (hL : L.Nodup)
    (ψ : Fin k → QState ((Fin n × Bool) × W)) :
    Run (workspaceBitOracle x) (L.flatMap fun j => StandardCopyCircuit j C)
      (TensorState χ (PiTensorState ψ)) =
    TensorState χ (PiTensorState fun j => if j ∈ L then Run (workspaceBitOracle x) C (ψ j)
      else ψ j) := by
  induction L generalizing ψ with
  | nil => simp
  | cons j L ih =>
    obtain ⟨hj, hnd⟩ := List.nodup_cons.mp hL
    simp only [List.flatMap_cons]
    rw [run_append, standardCopyCircuit_run, ih hnd]
    congr 2
    funext l
    by_cases hl : l = j
    · subst l; simp [hj]
    · simp [hl]

/-- For a unitary input circuit, the sequential copy circuit is unitary, has `k` times the
original query count and `k * GateCount C + 2*k*QueryCount C` gates, and acts independently
on all tensor factors while preserving the shared register. -/
theorem standardCopiesCircuit_spec (k : ℕ) (C : Circuit ((Fin n × Bool) × W))
    (hC : IsUnitaryCircuit C) :
    IsUnitaryCircuit (StandardCopiesCircuit k C) ∧
    QueryCount (StandardCopiesCircuit k C) = k * QueryCount C ∧
    GateCount (StandardCopiesCircuit k C) = k * GateCount C + 2 * k * QueryCount C ∧
    ∀ (x : Fin n → Bool) (χ : QState (Fin n × Bool))
      (ψ : Fin k → QState ((Fin n × Bool) × W)),
      Run (workspaceBitOracle x) (StandardCopiesCircuit k C) (TensorState χ (PiTensorState ψ)) =
      TensorState χ (PiTensorState fun j => Run (workspaceBitOracle x) C (ψ j)) := by
  refine ⟨copies_list_unitary hC _, ?_, ?_, ?_⟩
  · simpa [StandardCopiesCircuit] using copies_list_queries C (List.finRange k)
  · simpa [StandardCopiesCircuit, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm] using copies_list_gates C (List.finRange k)
  · intro x χ ψ
    simpa [StandardCopiesCircuit] using copies_list_run C x χ
      (List.finRange k) (List.nodup_finRange k) ψ

end Qatlib.Concepts.UniformBqp.OracleAmplify
