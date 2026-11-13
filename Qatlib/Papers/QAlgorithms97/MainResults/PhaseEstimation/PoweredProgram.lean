/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAlgorithms97.MainResults.InterferencePattern
import Qatlib.Concepts.QftPreparation.LocalQft
import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

/-!
# An explicit powered phase-estimation program

The instruction language `Instruction` separates controlled powers of a device matrix from known
local QFT gates. The program `word` implements Hadamard preparation, the controlled powers, and
an inverse QFT; its exact state and readout agree with the phase-estimation kernel discussed in
[CleveEtAl1998].

The resource counters treat each controlled power as one device call and count known local gates
separately. Normalization is preserved when the device matrix is unitary.

## Main statements

* `word_resources`: exact device-call and local-gate counts.
* `word_run`: the executed program produces the relabeled phase-estimation kernel.
* `word_readout`: the register probabilities are squared kernel amplitudes.

## References

* [Cleve et al., 1998][CleveEtAl1998]
-/

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

/-- A phase-estimation instruction consisting of either a controlled power indexed by a register
bit or a known local QFT gate. -/
inductive Instruction (m : ℕ) where
  | power (i : Fin m)
  | known (g : LocalQFTGate m)

/-- The gate applying `U ^ (2 ^ (m - 1 - i.val))` conditionally on bit `i` of the phase
register. -/
def powerMatrix {I : Type} [Fintype I] [DecidableEq I] (m : ℕ) (U : Matrix I I ℂ) (i : Fin m) :
    Matrix (Reg m × I) (Reg m × I) ℂ :=
  conditionalGate (fun x => U ^ (if x i then 2 ^ (m - 1 - i.val) else 0))

/-- The matrix interpretation of a powered-program instruction, using controlled device powers
or a local gate tensored with the target identity. -/
def instructionMatrix {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    (U : Matrix I I ℂ) : Instruction m → Matrix (Reg m × I) (Reg m × I) ℂ
  | .power i => powerMatrix m U i
  | .known g => TensorGate (localGateMatrix g) 1

/-- Execution of a list of instructions in order by applying their matrix interpretations to the
state. -/
def execute {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    (U : Matrix I I ℂ) : List (Instruction m) → QState (Reg m × I) → QState (Reg m × I)
  | [], ψ => ψ
  | s :: ss, ψ => execute U ss (ApplyGate (instructionMatrix U s) ψ)

/-- The number of controlled-power instructions in a program. -/
def deviceCalls {m : ℕ} : List (Instruction m) → ℕ
  | [] => 0
  | .power _ :: ss => 1 + deviceCalls ss
  | .known _ :: ss => deviceCalls ss

/-- The number of known local-gate instructions in a program. -/
def localGates {m : ℕ} : List (Instruction m) → ℕ
  | [] => 0
  | .power _ :: ss => localGates ss
  | .known _ :: ss => 1 + localGates ss

/-- The phase-estimation program with local Hadamards, one controlled power for each
phase-register bit, and an adjoint local QFT program. -/
def word (m : ℕ) : List (Instruction m) :=
  (localHadamard m).map Instruction.known ++
    (List.finRange m).map Instruction.power ++
      (localProgramAdjoint (localQFT m)).map Instruction.known

/-- Executing a concatenation of instruction lists equals executing the first list followed by
the second. -/
theorem execute_append {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    (U : Matrix I I ℂ) (ss tt : List (Instruction m)) (ψ : QState (Reg m × I)) :
    execute U (ss ++ tt) ψ = execute U tt (execute U ss ψ) := by
  induction ss generalizing ψ with
  | nil => rfl
  | cons s ss ih => exact ih _

/-- If the device matrix is unitary, every instruction matrix is unitary. -/
theorem instruction_unitary {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    {U : Matrix I I ℂ} (hU : U ∈ Matrix.unitaryGroup I ℂ) (s : Instruction m) :
    instructionMatrix U s ∈ Matrix.unitaryGroup (Reg m × I) ℂ := by
  cases s with
  | power i => exact conditionalGate_unitary _ (fun _ => (Matrix.unitaryGroup I ℂ).pow_mem hU _)
  | known g => exact tensorGate_unitary (localGateMatrix_unitary g) (Matrix.unitaryGroup I ℂ).one_mem

/-- Executing any instruction list with a unitary device matrix preserves normalization. -/
theorem execute_normalized {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    {U : Matrix I I ℂ} (hU : U ∈ Matrix.unitaryGroup I ℂ) (ss : List (Instruction m))
    {ψ : QState (Reg m × I)} (hψ : Normalized ψ) : Normalized (execute U ss ψ) := by
  induction ss generalizing ψ with
  | nil => exact hψ
  | cons s ss ih => exact ih (normalized_applyGate (instruction_unitary hU s) hψ)

/-- Executing only known local gates transforms the phase register by their program matrix and
leaves the target register unchanged. -/
theorem execute_local {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    (U : Matrix I I ℂ) (gs : List (LocalQFTGate m)) (α : QState (Reg m)) (ψ : QState I) :
    execute U (gs.map Instruction.known) (TensorState α ψ) =
      TensorState (ApplyGate (localProgramMatrix gs) α) ψ := by
  induction gs generalizing α with
  | nil => simp [execute]
  | cons g gs ih =>
    simp only [List.map_cons, execute, instructionMatrix, applyGate_tensorGate,
      applyGate_one, ih, localProgramMatrix_cons, applyGate_mul]

/-- A controlled family acting by scalar eigenvalues on a common target state transfers those
scalars to the control amplitudes. -/
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

/-- The sum of the binary place values whose listed control indices have true input bits,
counting repeated indices as listed. -/
def selectedWeight {m : ℕ} (x : Reg m) (js : List (Fin m)) : ℕ :=
  (js.map (fun j => if x j then 2 ^ (m - 1 - j.val) else 0)).sum

/-- On a device eigenstate with eigenvalue `lam`, executing the listed controlled powers
multiplies each control amplitude by `lam ^ selectedWeight x js` and leaves the target
unchanged. -/
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

/-- The selected weight over every register index equals the natural-number label given by
`bitVecEquiv`. -/
theorem selectedWeight_all (m : ℕ) (x : Reg m) :
    selectedWeight x (List.finRange m) = (bitVecEquiv m x).val := by
  rw [bitVecEquiv_binary_msb_expansion]
  simp only [selectedWeight, ← List.ofFn_eq_map, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  cases x i <;> simp

/-- Device-call and local-gate counts are additive under concatenation. -/
theorem counters_append {m : ℕ} (ss tt : List (Instruction m)) :
    deviceCalls (ss ++ tt) = deviceCalls ss + deviceCalls tt ∧
      localGates (ss ++ tt) = localGates ss + localGates tt := by
  induction ss with
  | nil => simp [deviceCalls, localGates]
  | cons s ss ih => cases s <;> simp [deviceCalls, localGates, ih.1, ih.2, Nat.add_assoc]

/-- A list of known local instructions has no device calls and has one local gate per list
entry. -/
theorem counters_known {m : ℕ} (gs : List (LocalQFTGate m)) :
    deviceCalls (gs.map Instruction.known) = 0 ∧ localGates (gs.map Instruction.known) = gs.length := by
  induction gs with
  | nil => exact ⟨rfl,rfl⟩
  | cons g gs ih => simpa [deviceCalls, localGates, Nat.add_comm] using ih

/-- A list of controlled-power instructions has one device call per entry and no known local
gates. -/
theorem counters_power {m : ℕ} (js : List (Fin m)) :
    deviceCalls (js.map Instruction.power) = js.length ∧ localGates (js.map Instruction.power) = 0 := by
  induction js with
  | nil => exact ⟨rfl,rfl⟩
  | cons j js ih => simp [deviceCalls, localGates, ih.1, ih.2, Nat.add_comm]

/-- The phase-estimation word has `m` device calls and `m + (m + m * (m - 1) / 2 + m / 2)` known
local gates. -/
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

/-- The uniform state weighted by the eigenphase raised to each binary label equals the
relabeled off-grid phase state. -/
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

/-- Relabeling a gate commutes with taking its conjugate transpose. -/
theorem relabelGate_adjoint {X Y : Type} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (e : X ≃ Y) (A : Matrix X X ℂ) :
    (relabelGate e A)ᴴ = relabelGate e (Aᴴ) := rfl

/-- On a device eigenstate with phase `φ`, the powered program produces the relabeled kernel
`qpeKernel (2 ^ m) φ` tensored with the unchanged eigenstate [CleveEtAl1998]. -/
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

/-- For a normalized device eigenstate, each phase-register outcome has probability equal to the
squared norm of the corresponding phase-estimation kernel amplitude. -/
theorem word_readout {I : Type} [Fintype I] [DecidableEq I] (m : ℕ)
    (U : Matrix I I ℂ) (φ : ℝ) (ψ : QState I) (hn : Normalized ψ)
    (hψ : U.mulVec ψ = Complex.exp (2 * Real.pi * Complex.I * φ) • ψ) (z : Reg m) :
    MeasureProb (execute U (word m) (TensorState (Ket (ZeroStr m)) ψ))
      ({z} ×ˢ (Finset.univ : Finset I)) = ‖qpeKernel (2 ^ m) φ (bitVecEquiv m z)‖ ^ 2 := by
  rw [word_run m U φ ψ hψ, measureProb_tensorState_left hn]
  simp only [MeasureProb, Finset.sum_singleton, BornProb, relabelState,
    Function.comp_apply, Equiv.symm_symm]

end Qatlib.Papers.QAlgorithms97.MainResults.PhaseEstimation.PoweredProgram
