/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Theorem1Stat
import Qatlib.Concepts.SearchStopping.KnownCount.Section3RotationSubgoal
import Qatlib.Concepts.SearchStopping.KnownCount.Theorem1Defs
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Foundations.PureStateMath.Reflection.Basic
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.SearchStopping.KnownCount

open Matrix
open Qatlib.Concepts.SearchStopping.KnownCount

theorem theorem1 : Theorem1 := diffusion_eq_hadamardN_zeroPhaseReflection

theorem zeroPhaseReflection_unitary (n : ℕ) :
    ZeroPhaseReflection n ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  have h : ZeroPhaseReflection n = PhaseOracle (fun x : Reg n => decide (x ≠ ZeroStr n)) := by
    ext x y
    simp only [ZeroPhaseReflection, PhaseOracle, Matrix.diagonal_apply]
    by_cases hxy : x = y <;> by_cases hx : x = ZeroStr n <;> simp [hxy, hx]
  rw [h]
  exact phaseOracle_unitary _

theorem diffusionCircuit_valid (n : ℕ) : IsUnitaryCircuit (DiffusionCircuit n) := by
  simp [DiffusionCircuit, hadamardN_unitary, zeroPhaseReflection_unitary]

theorem run_diffusionCircuit (n : ℕ) (O : Matrix (Reg n) (Reg n) ℂ)
    (ψ : QState (Reg n)) :
    Run O (DiffusionCircuit n) ψ = ApplyGate (Diffusion (Reg n)) ψ := by
  simp only [DiffusionCircuit, run_gate, run_nil]
  rw [diffusion_eq_hadamardN_zeroPhaseReflection, applyGate_mul, applyGate_mul]

theorem diffusionCircuit_counts (n : ℕ) :
    QueryCount (DiffusionCircuit n) = 0 ∧ GateCount (DiffusionCircuit n) = 3 := by
  exact ⟨rfl, rfl⟩

theorem run_expandedStep (n : ℕ) (O : Matrix (Reg n) (Reg n) ℂ)
    (ψ : QState (Reg n)) :
    Run O (ExpandedStep n) ψ = Run O (GroverStep (Reg n)) ψ := by
  simp only [ExpandedStep, run_query, run_diffusionCircuit, GroverStep, run_gate, run_nil]

theorem run_expandedCircuit (n j : ℕ) (O : Matrix (Reg n) (Reg n) ℂ)
    (ψ : QState (Reg n)) :
    Run O (ExpandedCircuit n j) ψ = Run O (GroverCircuit (Reg n) j) ψ := by
  induction j generalizing ψ with
  | zero => rfl
  | succ j ih =>
    change Run O (ExpandedStep n ++ ExpandedCircuit n j) ψ =
      Run O (GroverStep (Reg n) ++ GroverCircuit (Reg n) j) ψ
    rw [run_append, run_append, ih, run_expandedStep]

theorem expandedCircuit_valid (n j : ℕ) : IsUnitaryCircuit (ExpandedCircuit n j) := by
  apply IsUnitaryCircuit.repeatCircuit
  simpa only [ExpandedStep, isUnitaryCircuit_query] using diffusionCircuit_valid n

theorem expandedCircuit_counts (n j : ℕ) :
    QueryCount (ExpandedCircuit n j) = j ∧
    GateCount (ExpandedCircuit n j) = 3 * j ∧ Size (ExpandedCircuit n j) = 4 * j := by
  unfold ExpandedCircuit
  rw [queryCount_repeatCircuit, gateCount_repeatCircuit, size_repeatCircuit]
  simp [ExpandedStep, DiffusionCircuit, GateCount, Size, Nat.mul_comm]

theorem expandedCircuit_normalized (n j : ℕ) (A : Finset (Reg n)) :
    Normalized (Run (SetOracle A) (ExpandedCircuit n j) (Uniform (Reg n))) := by
  rw [run_expandedCircuit]
  exact normalized_groverState (Fintype.card_pos) A j

theorem expandedCircuit_success (n j : ℕ) (A : Finset (Reg n)) (θ : ℝ)
    (hθ : (Real.sin θ) ^ 2 = (A.card : ℝ) / (Fintype.card (Reg n) : ℝ))
    (hs : Real.sin θ ≠ 0) (hc : Real.cos θ ≠ 0) :
    MeasureProb (Run (SetOracle A) (ExpandedCircuit n j) (Uniform (Reg n))) A =
      (Real.sin ((2 * j + 1) * θ)) ^ 2 := by
  rw [run_expandedCircuit]
  exact measureProb_groverState (Fintype.card_pos) A θ hθ hs hc j

end Qatlib.Concepts.SearchStopping.KnownCount
