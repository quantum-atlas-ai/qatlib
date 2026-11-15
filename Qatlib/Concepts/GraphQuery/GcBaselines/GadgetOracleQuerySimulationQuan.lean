/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.GraphQuery.GcBaselines.GadgetOracleQuerySimulationStat

@[expose] public section
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Concepts.GraphQuery.GcBaselines
open Matrix
open scoped Classical

variable {W : Type} [Fintype W] [DecidableEq W]

/-- Expresses gadget adjacency as either a fixed baseline bit or the input bit selected by its
variable role. -/
theorem gadgetAdjAt_role {n : ℕ} (adj : Fin n → Fin n → Bool) (x : Fin n → Fin n → Bool)
    (v w : GadgetVertex n) :
    gadgetAdjAt adj x v w = (gadgetVariableRole v w).elim
      (gadgetAdjAt adj (fun _ _ => false) v w) (fun p => x p.1 p.2) := by
  cases v with
  | station =>
    cases w with
    | station => rfl
    | layer ℓ j => fin_cases ℓ <;> simp [gadgetAdjAt, gadgetVariableRole]
  | layer ℓ1 j =>
    cases w with
    | station => fin_cases ℓ1 <;> simp [gadgetAdjAt, gadgetVariableRole]
    | layer ℓ2 k => fin_cases ℓ1 <;> fin_cases ℓ2 <;> simp [gadgetAdjAt, gadgetVariableRole]

/-- Expresses a gadget oracle bit using its address role and the fixed baseline oracle. -/
theorem gadgetOracleBit_role {n : ℕ} (adj : Fin n → Fin n → Bool) (x : Fin n → Fin n → Bool)
    (a : Fin (gadgetAddrCount n)) :
    gadgetOracleBit adj x a = (gadgetAddressRole n a).elim
      (gadgetOracleBit adj (fun _ _ => false) a) (fun p => x p.1 p.2) := by
  simp only [gadgetOracleBit, gadgetAddressRole]
  exact gadgetAdjAt_role adj x _ _

/-- Identifies a variable gadget oracle bit with the source bit selected by its address role. -/
theorem gadgetOracleBit_role_some {n : ℕ} (adj : Fin n → Fin n → Bool)
    (x : Fin n → Fin n → Bool) (a : Fin (gadgetAddrCount n)) (p : Fin n × Fin n)
    (h : gadgetAddressRole n a = some p) :
    gadgetOracleBit adj x a = x p.1 p.2 := by
  rw [gadgetOracleBit_role adj x a, h]; simp

/-- Shows that a gadget address with no variable role returns its fixed baseline bit. -/
theorem gadgetOracleBit_role_none {n : ℕ} (adj : Fin n → Fin n → Bool)
    (x : Fin n → Fin n → Bool) (a : Fin (gadgetAddrCount n))
    (h : gadgetAddressRole n a = none) :
    gadgetOracleBit adj x a = gadgetOracleBit adj (fun _ _ => false) a := by
  rw [gadgetOracleBit_role adj x a, h]; simp

/-- Evaluates source labels at an address encoded by `finProdFinEquiv`. -/
theorem gadgetSourceLabels_finProdFinEquiv {n : ℕ} (x : Fin n → Fin n → Bool)
    (p : Fin n × Fin n) :
    gadgetSourceLabels n x (finProdFinEquiv p) = x p.1 p.2 := by
  simp [gadgetSourceLabels]

omit [Fintype W] [DecidableEq W] in
/-- Shows that the source address routing swap is an involution when `n` is positive. -/
theorem gadgetAddressRoute_involutive [Fintype W] [DecidableEq W] (n : ℕ) (hn : 0 < n) :
    Function.Involutive (fun p : GadgetSourceRegister n W =>
      (((Equiv.swap (gadgetSourceZero n hn).1 (gadgetSourceAddress n hn p.2.1.1)) p.1.1,
        p.1.2), p.2)) := by
  intro p
  simp [Equiv.swap_apply_self]

/-- Shows that `gadgetAddressRoute` is unitary when `n` is positive. -/
theorem gadgetAddressRoute_unitary (n : ℕ) (hn : 0 < n) :
    gadgetAddressRoute n hn ∈ Matrix.unitaryGroup (GadgetSourceRegister n W) ℂ :=
  permMatrix_unitary (gadgetAddressRoute_involutive n hn)

/-- Computes the action of the gadget address routing gate on state coordinates. -/
theorem applyGate_gadgetAddressRoute (n : ℕ) (hn : 0 < n)
    (φ : QState (GadgetSourceRegister n W)) (p : GadgetSourceRegister n W) :
    ApplyGate (gadgetAddressRoute n hn) φ p =
      φ (((Equiv.swap (gadgetSourceZero n hn).1 (gadgetSourceAddress n hn p.2.1.1)) p.1.1,
        p.1.2), p.2) :=
  applyGate_permMatrix (gadgetAddressRoute_involutive n hn) φ p

omit [Fintype W] [DecidableEq W] in
/-- Shows that the conditional target-bit mask is an involution. -/
theorem gadgetMaskTarget_involutive [Fintype W] [DecidableEq W] (n : ℕ)
    (adj : Fin n → Fin n → Bool) :
    Function.Involutive (fun p : GadgetSourceRegister n W =>
      (p.1, ((p.2.1.1, p.2.1.2 ^^ (if (gadgetAddressRole n p.2.1.1).isSome then p.1.2
        else gadgetOracleBit adj (fun _ _ => false) p.2.1.1)), p.2.2))) := by
  intro p
  simp only
  rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- Shows that `gadgetMaskTarget` is unitary. -/
theorem gadgetMaskTarget_unitary (n : ℕ) (adj : Fin n → Fin n → Bool) :
    gadgetMaskTarget n adj ∈ Matrix.unitaryGroup (GadgetSourceRegister n W) ℂ :=
  permMatrix_unitary (gadgetMaskTarget_involutive n adj)

/-- Computes the action of the gadget target masking gate on state coordinates. -/
theorem applyGate_gadgetMaskTarget (n : ℕ) (adj : Fin n → Fin n → Bool)
    (φ : QState (GadgetSourceRegister n W)) (p : GadgetSourceRegister n W) :
    ApplyGate (gadgetMaskTarget n adj) φ p =
      φ (p.1, ((p.2.1.1, p.2.1.2 ^^ (if (gadgetAddressRole n p.2.1.1).isSome then p.1.2
        else gadgetOracleBit adj (fun _ _ => false) p.2.1.1)), p.2.2)) :=
  applyGate_permMatrix (gadgetMaskTarget_involutive n adj) φ p

/-- Shows that a compiled query simulates the gadget oracle and restores the source ancilla to
its initial basis state. -/
theorem gadgetCompileStep_query_run {n : ℕ} (hn : 0 < n) (adj : Fin n → Fin n → Bool)
    (x : Fin n → Fin n → Bool) (ψ : QState (GadgetHostRegister n W)) :
    Run (workspaceBitOracle (W := GadgetHostRegister n W) (gadgetSourceLabels n x))
        (gadgetCompileStep n hn adj Step.query)
        (TensorState (Ket (gadgetSourceZero n hn)) ψ) =
      TensorState (Ket (gadgetSourceZero n hn))
        (ApplyGate (workspaceBitOracle (W := W) (gadgetOracleBit adj x)) ψ) := by
  funext p
  rcases p with ⟨⟨sa, sb⟩, ha, w⟩
  rcases ha with ⟨ha, hb⟩
  simp only [gadgetCompileStep, run_gate, run_query, run_nil,
    applyGate_gadgetAddressRoute, applyGate_workspaceBitOracle_mk,
    applyGate_gadgetMaskTarget, applyGate_workspaceBitOracle_mk,
    applyGate_gadgetAddressRoute]
  rw [Equiv.swap_apply_self, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
  by_cases hz : (sa, sb) = gadgetSourceZero n hn
  · simp only [gadgetSourceZero, Prod.mk.injEq] at hz
    obtain ⟨h1, h2⟩ := hz
    subst h1
    subst h2
    simp only [TensorState, Ket, gadgetSourceZero, ite_eq_left, one_mul,
      applyGate_workspaceBitOracle_mk]
    rcases hrole : gadgetAddressRole n ha with _ | ⟨b, a'⟩
    · rw [gadgetOracleBit_role_none adj x ha hrole]
      split
      · next hcontra => exact absurd hcontra (by simp)
      · rfl
    · have hs : gadgetSourceAddress n hn ha = finProdFinEquiv (b, a') := by
        rw [gadgetSourceAddress, hrole]; simp
      rw [gadgetOracleBit_role_some adj x ha (b, a') hrole]
      split
      · rw [Equiv.swap_apply_left, hs, gadgetSourceLabels_finProdFinEquiv, Bool.false_xor]
      · next hcontra => exact absurd (by simp) hcontra
  · simp [TensorState, Ket, hz]

/-- Shows that the compiled circuit simulates the original gadget oracle circuit while restoring
the source ancilla. -/
theorem gadgetCompileCircuit_run {n : ℕ} (hn : 0 < n) (adj : Fin n → Fin n → Bool)
    (x : Fin n → Fin n → Bool) :
    ∀ (C : Circuit (GadgetHostRegister n W)) (ψ : QState (GadgetHostRegister n W)),
      Run (workspaceBitOracle (W := GadgetHostRegister n W) (gadgetSourceLabels n x))
          (gadgetCompileCircuit n hn adj C) (TensorState (Ket (gadgetSourceZero n hn)) ψ) =
        TensorState (Ket (gadgetSourceZero n hn))
          (Run (workspaceBitOracle (W := W) (gadgetOracleBit adj x)) C ψ) := by
  intro C
  induction C with
  | nil => intro ψ; rfl
  | cons s C ih =>
    intro ψ
    have hflat : gadgetCompileCircuit n hn adj (s :: C) =
        gadgetCompileStep n hn adj s ++ gadgetCompileCircuit n hn adj C := rfl
    rw [hflat, run_append]
    cases s with
    | gate U =>
      have hg : Run (workspaceBitOracle (W := GadgetHostRegister n W) (gadgetSourceLabels n x))
          (gadgetCompileStep n hn adj (Step.gate U))
          (TensorState (Ket (gadgetSourceZero n hn)) ψ) =
          TensorState (Ket (gadgetSourceZero n hn)) (ApplyGate U ψ) := by
        simp only [gadgetCompileStep, run_gate, run_nil, applyGate_tensorGate, applyGate_one]
      rw [hg]
      exact ih (ApplyGate U ψ)
    | query =>
      rw [gadgetCompileStep_query_run hn adj x ψ]
      exact ih (ApplyGate (workspaceBitOracle (W := W) (gadgetOracleBit adj x)) ψ)

/-- Shows that gadget circuit compilation doubles the query count. -/
theorem gadgetCompileCircuit_queryCount {n : ℕ} (hn : 0 < n) (adj : Fin n → Fin n → Bool)
    (C : Circuit (GadgetHostRegister n W)) :
    QueryCount (gadgetCompileCircuit n hn adj C) = 2 * QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    have hflat : gadgetCompileCircuit n hn adj (s :: C) =
        gadgetCompileStep n hn adj s ++ gadgetCompileCircuit n hn adj C := rfl
    rw [hflat, queryCount_append]
    cases s with
    | gate U =>
      show (0 : ℕ) + QueryCount (gadgetCompileCircuit n hn adj C) = 2 * QueryCount C
      rw [ih]; omega
    | query =>
      show (2 : ℕ) + QueryCount (gadgetCompileCircuit n hn adj C) = 2 * (QueryCount C + 1)
      rw [ih]; omega

/-- Shows that gadget circuit compilation adds three gates per original query. -/
theorem gadgetCompileCircuit_gateCount {n : ℕ} (hn : 0 < n) (adj : Fin n → Fin n → Bool)
    (C : Circuit (GadgetHostRegister n W)) :
    GateCount (gadgetCompileCircuit n hn adj C) = GateCount C + 3 * QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    have hflat : gadgetCompileCircuit n hn adj (s :: C) =
        gadgetCompileStep n hn adj s ++ gadgetCompileCircuit n hn adj C := rfl
    rw [hflat, gateCount_append]
    cases s with
    | gate U =>
      show (1 : ℕ) + GateCount (gadgetCompileCircuit n hn adj C) =
          (GateCount C + 1) + 3 * QueryCount C
      rw [ih]; omega
    | query =>
      show (3 : ℕ) + GateCount (gadgetCompileCircuit n hn adj C) = GateCount C + 3 *
          (QueryCount C + 1)
      rw [ih]; omega

/-- Shows that gadget circuit compilation preserves unitarity. -/
theorem gadgetCompileCircuit_isUnitary {n : ℕ} (hn : 0 < n) (adj : Fin n → Fin n → Bool) :
    ∀ (C : Circuit (GadgetHostRegister n W)), IsUnitaryCircuit C →
      IsUnitaryCircuit (gadgetCompileCircuit n hn adj C) := by
  intro C
  induction C with
  | nil => intro _; exact isUnitaryCircuit_nil
  | cons s C ih =>
    intro hC
    have hflat : gadgetCompileCircuit n hn adj (s :: C) =
        gadgetCompileStep n hn adj s ++ gadgetCompileCircuit n hn adj C := rfl
    rw [hflat, isUnitaryCircuit_append]
    cases s with
    | gate U =>
      obtain ⟨hU, hC'⟩ := (isUnitaryCircuit_gate U C).mp hC
      simp only [gadgetCompileStep, isUnitaryCircuit_gate, isUnitaryCircuit_nil, and_true]
      exact ⟨tensorGate_unitary (Submonoid.one_mem _) hU, ih hC'⟩
    | query =>
      obtain hC' := (isUnitaryCircuit_query C).mp hC
      simp only [gadgetCompileStep, isUnitaryCircuit_gate, isUnitaryCircuit_query,
        isUnitaryCircuit_nil, and_true]
      exact ⟨⟨gadgetAddressRoute_unitary n hn, gadgetMaskTarget_unitary n adj,
        gadgetAddressRoute_unitary n hn⟩, ih hC'⟩

/-- Establishes the gadget oracle query simulation specified by `GadgetOracleQuerySimulation`. -/
theorem gadgetOracleQuerySimulation : GadgetOracleQuerySimulation := by
  intro W _ _ n hn adj C
  refine ⟨fun hC => gadgetCompileCircuit_isUnitary hn adj C hC,
    gadgetCompileCircuit_queryCount hn adj C,
    gadgetCompileCircuit_gateCount hn adj C, ?_⟩
  intro x ψ
  refine ⟨gadgetCompileCircuit_run hn adj x C ψ, ?_⟩
  intro E
  rw [gadgetCompileCircuit_run hn adj x C ψ,
    measureProb_tensorState_right (normalized_ket (gadgetSourceZero n hn))]

end Qatlib.Concepts.GraphQuery.GcBaselines
