/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAlgorithms97.MainResults.InterferencePattern
import Qatlib.Concepts.QftPreparation.LocalQft
import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QAlgorithms97.MainResults.PhaseEstimation.PoweredProgram
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Papers.QAlgorithms97.MainResults.InterferencePattern

inductive Instruction (m : ℕ) where
  | power (i : Fin m)
  | known (g : LocalQFTGate m)

def powerMatrix {I : Type} [Fintype I] [DecidableEq I] (m : ℕ) (U : Matrix I I ℂ) (i : Fin m) :
    Matrix (Reg m × I) (Reg m × I) ℂ :=
  conditionalGate (fun x => U ^ (if x i then 2 ^ (m - 1 - i.val) else 0))

def instructionMatrix {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    (U : Matrix I I ℂ) : Instruction m → Matrix (Reg m × I) (Reg m × I) ℂ
  | .power i => powerMatrix m U i
  | .known g => TensorGate (localGateMatrix g) 1

def execute {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    (U : Matrix I I ℂ) : List (Instruction m) → QState (Reg m × I) → QState (Reg m × I)
  | [], ψ => ψ
  | s :: ss, ψ => execute U ss (ApplyGate (instructionMatrix U s) ψ)

def deviceCalls {m : ℕ} : List (Instruction m) → ℕ
  | [] => 0
  | .power _ :: ss => 1 + deviceCalls ss
  | .known _ :: ss => deviceCalls ss

def localGates {m : ℕ} : List (Instruction m) → ℕ
  | [] => 0
  | .power _ :: ss => localGates ss
  | .known _ :: ss => 1 + localGates ss

def word (m : ℕ) : List (Instruction m) :=
  (localHadamard m).map Instruction.known ++
    (List.finRange m).map Instruction.power ++
      (localProgramAdjoint (localQFT m)).map Instruction.known

theorem execute_append {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    (U : Matrix I I ℂ) (ss tt : List (Instruction m)) (ψ : QState (Reg m × I)) :
    execute U (ss ++ tt) ψ = execute U tt (execute U ss ψ) := by
  induction ss generalizing ψ with
  | nil => rfl
  | cons s ss ih => exact ih _

theorem instruction_unitary {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    {U : Matrix I I ℂ} (hU : U ∈ Matrix.unitaryGroup I ℂ) (s : Instruction m) :
    instructionMatrix U s ∈ Matrix.unitaryGroup (Reg m × I) ℂ := by
  cases s with
  | power i => exact conditionalGate_unitary _ (fun _ => (Matrix.unitaryGroup I ℂ).pow_mem hU _)
  | known g => exact tensorGate_unitary (localGateMatrix_unitary g) (Matrix.unitaryGroup I ℂ).one_mem

theorem execute_normalized {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    {U : Matrix I I ℂ} (hU : U ∈ Matrix.unitaryGroup I ℂ) (ss : List (Instruction m))
    {ψ : QState (Reg m × I)} (hψ : Normalized ψ) : Normalized (execute U ss ψ) := by
  induction ss generalizing ψ with
  | nil => exact hψ
  | cons s ss ih => exact ih (normalized_applyGate (instruction_unitary hU s) hψ)

theorem execute_local {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    (U : Matrix I I ℂ) (gs : List (LocalQFTGate m)) (α : QState (Reg m)) (ψ : QState I) :
    execute U (gs.map Instruction.known) (TensorState α ψ) =
      TensorState (ApplyGate (localProgramMatrix gs) α) ψ := by
  induction gs generalizing α with
  | nil => simp [execute]
  | cons g gs ih =>
    simp only [List.map_cons, execute, instructionMatrix, applyGate_tensorGate,
      applyGate_one, ih, localProgramMatrix_cons, applyGate_mul]

theorem conditional_scalar {X I : Type} [Fintype X] [DecidableEq X]
    [Fintype I] [DecidableEq I] (V : X → Matrix I I ℂ) (lam : X → ℂ)
    (ψ : QState I) (hψ : ∀ x, ApplyGate (V x) ψ = lam x • ψ) (α : QState X) :
    ApplyGate (conditionalGate V) (TensorState α ψ) =
      TensorState (fun x => lam x * α x) ψ := by
  funext p
  rcases p with ⟨x,y⟩
  have h := congrFun (hψ x) y
  change (∑ z, V x y z * ψ z) = lam x * ψ y at h
  change (∑ q : X × I, (if x = q.1 then V x y q.2 else 0) * (α q.1 * ψ q.2)) = _
  rw [Fintype.sum_prod_type]
  simp only [ite_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  simp_rw [show ∀ z, V x y z * (α x * ψ z) = α x * (V x y z * ψ z) by intro z; ring]
  rw [← Finset.mul_sum, h]
  simp only [TensorState]
  ring

def selectedWeight {m : ℕ} (x : Reg m) (js : List (Fin m)) : ℕ :=
  (js.map (fun j => if x j then 2 ^ (m - 1 - j.val) else 0)).sum

theorem execute_powers {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    (U : Matrix I I ℂ) (lam : ℂ) (ψ : QState I) (hψ : U.mulVec ψ = lam • ψ)
    (js : List (Fin m)) (α : QState (Reg m)) :
    execute U (js.map Instruction.power) (TensorState α ψ) =
      TensorState (fun x => lam ^ selectedWeight x js * α x) ψ := by
  induction js generalizing α with
  | nil => simp [execute, selectedWeight]
  | cons j js ih =>
    simp only [List.map_cons, execute, instructionMatrix, powerMatrix]
    rw [conditional_scalar _ (fun x => lam ^ (if x j then 2 ^ (m - 1 - j.val) else 0)) ψ
      (fun x => mulVec_pow_of_eigen hψ _) α, ih]
    congr 1
    funext x
    simp only [selectedWeight, List.map_cons, List.sum_cons, pow_add]
    ring

theorem selectedWeight_all (m : ℕ) (x : Reg m) :
    selectedWeight x (List.finRange m) = (bitVecEquiv m x).val := by
  rw [bitVecEquiv_binary_msb_expansion]
  simp only [selectedWeight, ← List.ofFn_eq_map, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  cases x i <;> simp

theorem counters_append {m : ℕ} (ss tt : List (Instruction m)) :
    deviceCalls (ss ++ tt) = deviceCalls ss + deviceCalls tt ∧
      localGates (ss ++ tt) = localGates ss + localGates tt := by
  induction ss with
  | nil => simp [deviceCalls, localGates]
  | cons s ss ih => cases s <;> simp [deviceCalls, localGates, ih.1, ih.2, Nat.add_assoc]

theorem counters_known {m : ℕ} (gs : List (LocalQFTGate m)) :
    deviceCalls (gs.map Instruction.known) = 0 ∧ localGates (gs.map Instruction.known) = gs.length := by
  induction gs with
  | nil => exact ⟨rfl,rfl⟩
  | cons g gs ih => simpa [deviceCalls, localGates, Nat.add_comm] using ih

theorem counters_power {m : ℕ} (js : List (Fin m)) :
    deviceCalls (js.map Instruction.power) = js.length ∧ localGates (js.map Instruction.power) = 0 := by
  induction js with
  | nil => exact ⟨rfl,rfl⟩
  | cons j js ih => simp [deviceCalls, localGates, ih.1, ih.2, Nat.add_comm]

theorem word_resources (m : ℕ) :
    deviceCalls (word m) = m ∧
      localGates (word m) = m + (m + m * (m - 1) / 2 + m / 2) := by
  obtain ⟨_, _, _, _, _, _, hg, _, _⟩ :=
    localDyadicProgram_run_adjoint_cost m (localQFT m) (Ket (ZeroStr m))
  have hq := (Qatlib.Concepts.QftPreparation.LocalQft.aqLocalQFT_actual_matrix_and_cost m).2.1
  rw [hg] at hq
  simp only [word, (counters_append _ _).1, (counters_append _ _).2,
    (counters_known _).1, (counters_known _).2, (counters_power _).1, (counters_power _).2,
    List.length_finRange, localHadamard_length, localProgramAdjoint, List.length_map,
    List.length_reverse, hq]
  omega

theorem accumulated_phase (m : ℕ) (φ : ℝ) :
    (fun x : Reg m => Complex.exp (2 * Real.pi * Complex.I * φ) ^ (bitVecEquiv m x).val *
      Uniform (Reg m) x) = relabelState (bitVecEquiv m).symm (offGridPhase (2 ^ m) φ) := by
  funext x
  simp only [Uniform, card_reg, relabelState, Function.comp_apply, Equiv.symm_symm,
    offGridPhase, ← Complex.exp_nat_mul]
  rw [mul_comm]
  congr 2
  push_cast
  ring

theorem relabelGate_adjoint {X Y : Type} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (e : X ≃ Y) (A : Matrix X X ℂ) :
    (relabelGate e A)ᴴ = relabelGate e (Aᴴ) := rfl

theorem word_run {I : Type} [Fintype I] [DecidableEq I] (m : ℕ)
    (U : Matrix I I ℂ) (φ : ℝ) (ψ : QState I)
    (hψ : U.mulVec ψ = Complex.exp (2 * Real.pi * Complex.I * φ) • ψ) :
    execute U (word m) (TensorState (Ket (ZeroStr m)) ψ) =
      TensorState (relabelState (bitVecEquiv m).symm (qpeKernel (2 ^ m) φ)) ψ := by
  rw [word, execute_append, execute_append, execute_local, localProgramMatrix_localHadamard,
    applyGate_hadamardN_ket_zero, execute_powers U _ ψ hψ]
  simp_rw [selectedWeight_all]
  rw [accumulated_phase, execute_local]
  have ha := (localDyadicProgram_run_adjoint_cost m (localQFT m) (Ket (ZeroStr m))).2.1
  rw [ha, (Qatlib.Concepts.QftPreparation.LocalQft.aqLocalQFT_actual_matrix_and_cost m).1,
    relabelGate_adjoint, applyGate_relabelGate]
  rfl

theorem word_readout {I : Type} [Fintype I] [DecidableEq I] (m : ℕ)
    (U : Matrix I I ℂ) (φ : ℝ) (ψ : QState I) (hn : Normalized ψ)
    (hψ : U.mulVec ψ = Complex.exp (2 * Real.pi * Complex.I * φ) • ψ) (z : Reg m) :
    MeasureProb (execute U (word m) (TensorState (Ket (ZeroStr m)) ψ))
      ({z} ×ˢ (Finset.univ : Finset I)) = ‖qpeKernel (2 ^ m) φ (bitVecEquiv m z)‖ ^ 2 := by
  rw [word_run m U φ ψ hψ, measureProb_tensorState_left hn]
  simp only [MeasureProb, Finset.sum_singleton, BornProb, relabelState,
    Function.comp_apply, Equiv.symm_symm]

end Qatlib.Papers.QAlgorithms97.MainResults.PhaseEstimation.PoweredProgram
