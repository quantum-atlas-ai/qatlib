/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QAlgorithms97.MainResults.DeutschJozsa
public import Qatlib.Concepts.CircuitLang.QueryWords
public import Qatlib.Concepts.CircuitLang.LocGates
public import Qatlib.Concepts.CircuitLang.WireReg
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! The pure-unitary word semantics are checked using the Deutsch-Jozsa word `djCircuit`.
Order is checked with non-commuting gates, duplicated target wires are rejected, and
disjoint-block placements commute. Counts refer to query words, not a compiled finite
elementary gate set. -/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Papers.QAlgorithms97.MainResults.DeutschJozsa
open Qatlib.Concepts.CircuitLang.QueryWords
open Qatlib.Concepts.CircuitLang.LocGates
open Qatlib.Concepts.CircuitLang.WireReg

namespace QatlibTests.ToolkitCircuit

/-- The Deutsch-Jozsa word denotes the bit oracle conjugated by the lifted Hadamards. -/
theorem dj_denote {n : ℕ} (f : Reg n → Bool) :
    Denote (BitOracleOn f) (djCircuit n)
      = LiftGate (HadamardN n) * BitOracleOn f * LiftGate (HadamardN n) := by
  simp [Denote, InstMat, djCircuit]

/-- The denoted Deutsch-Jozsa word prepares the
interference state, uses one query, and denotes a unitary matrix. -/
theorem dj_bridge {n : ℕ} (f : Reg n → Bool) :
    ApplyGate (Denote (BitOracleOn f) (djCircuit n)) (TensorState (Ket (ZeroStr n)) Minus)
      = TensorState (djFinalState f) Minus ∧
    QueryCount (djCircuit n) = 1 ∧
    Denote (BitOracleOn f) (djCircuit n) ∈ Matrix.unitaryGroup (Reg n × Bool) ℂ := by
  refine ⟨?_, (dj_circuit_run f).2, denote_unitary _ (bitOracleOn_unitary f) ?_⟩
  · rw [← run_denote]
    exact (dj_circuit_run f).1
  · have hU : LiftGate (HadamardN n) ∈ Matrix.unitaryGroup (Reg n × Bool) ℂ :=
      liftGate_unitary (hadamardN_unitary n)
    show IsUnitaryCircuit [Step.gate (LiftGate (HadamardN n)), Step.query,
      Step.gate (LiftGate (HadamardN n))]
    rw [isUnitaryCircuit_gate, isUnitaryCircuit_query, isUnitaryCircuit_gate]
    exact ⟨hU, hU, isUnitaryCircuit_nil⟩

/-- The pair word denotes the product with the first-executed gate rightmost. -/
theorem denote_xz :
    Denote (1 : Matrix Bool Bool ℂ) [Step.gate PauliX, Step.gate PauliZ] = PauliZ * PauliX :=
  denote_pair _ _ _

/-- Executing Pauli X then Pauli Z sends `Ket false` to `-Ket true`. -/
theorem word_order_xz :
    Run (1 : Matrix Bool Bool ℂ) [Step.gate PauliX, Step.gate PauliZ] (Ket false)
      = fun b => (-1 : ℂ) * Ket true b := by
  simp only [Run]
  rw [applyGate_pauliX_ket, PauliZ, applyGate_diagonal]
  funext b
  cases b <;> simp [Ket]

/-- Executing Pauli Z then Pauli X sends `Ket false` to `Ket true`. -/
theorem word_order_zx :
    Run (1 : Matrix Bool Bool ℂ) [Step.gate PauliZ, Step.gate PauliX] (Ket false)
      = Ket true := by
  simp only [Run]
  have hz : ApplyGate PauliZ (Ket false) = Ket false := by
    rw [PauliZ, applyGate_diagonal]
    funext b
    cases b <;> simp [Ket]
  rw [hz, applyGate_pauliX_ket]
  rfl

/-- Since the two word orders give different states, word order is execution order and not
the reversed matrix product. -/
theorem order_regress :
    Run (1 : Matrix Bool Bool ℂ) [Step.gate PauliX, Step.gate PauliZ] (Ket false) ≠
      Run (1 : Matrix Bool Bool ℂ) [Step.gate PauliZ, Step.gate PauliX] (Ket false) := by
  rw [word_order_xz, word_order_zx]
  intro h
  have ht := congrFun h true
  simp only [Ket] at ht
  norm_num at ht

/-- Regression: the duplicated wire selection is rejected by injectivity. -/
theorem dup_rejected : ¬ Function.Injective dupSel :=
  dupSel_not_inj

/-- Regression: the canonical last-wire selection on a two-wire register targets wire one. -/
theorem lastSel_2_1 : ((lastSel 1 1).sel 0 : Wire 2) = 1 := rfl

/-- Regression: on a register split into two disjoint wire blocks, a gate on each block
commutes with a gate on the other block. -/
theorem placed_comm_reg (U : Matrix (Reg 2) (Reg 2) ℂ) (V : Matrix (Reg 1) (Reg 1) ℂ) :
    PlacedFirst 2 1 U * PlacedLast 2 1 V = PlacedLast 2 1 V * PlacedFirst 2 1 U :=
  placedComm 2 1 U V

/-- Regression: placing the two-bit Hadamard on the first two of three wires is unitary. -/
theorem placed_H2_uni :
    PlacedFirst 2 1 (HadamardN 2) ∈ Matrix.unitaryGroup (Reg (2 + 1)) ℂ :=
  placedFirst_uni (hadamardN_unitary 2)

/-- Regression: reindexing a register matrix to `Fin (2 ^ n)` and back is the identity. -/
theorem reidx_round_1 :
    ReidxReg 1 (Matrix.reindex (bitVecEquiv 1) (bitVecEquiv 1) (HadamardN 1)) = HadamardN 1 :=
  reidxReg_round 1 _

/-- Regression: unitarity is preserved by the `Fin (2 ^ n)` transport. -/
theorem reidx_unit_wit :
    Matrix.reindex (bitVecEquiv 1) (bitVecEquiv 1) (HadamardN 1)
      ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  reidxUnitary _ (hadamardN_unitary 1)

end QatlibTests.ToolkitCircuit
