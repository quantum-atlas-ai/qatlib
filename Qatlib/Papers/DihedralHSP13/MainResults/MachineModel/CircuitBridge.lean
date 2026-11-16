/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PureStateMath.Qubit
public import Qatlib.Foundations.QueryWordCore.Circuit
public import Qatlib.Papers.DihedralHSP13.MainResults.MachineModel.SourceMachineEquivalence

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Instruction-stream compilation related to Kuperberg 2013, Proposition 2.1

Source: Greg Kuperberg, *Another subexponential-time quantum algorithm for the dihedral
hidden subgroup problem*, arXiv:1112.3333v1 (TQC 2013), Proposition 2.1, Section 2,
page 2 (txt line 79, PDF p. 2).

The proposition states that the gate complexity of a classically uniform family of quantum
circuits is equivalent, up to a constant factor, to the computation time of a RAM-type
machine with a classical address register, a quantum data register, a classical tape, and a
quantum tape.

## What is formalized here

The paper's proof is a per-gate compilation in both directions together with a final
measurement of the acceptance bit.  This file isolates the *instruction level* of that
compilation, where it can be carried out exactly:

* `MachineInstr` and `runProgram` give the operational semantics of the machine's quantum
  data register: a program is a list of data-register instructions, each of which is either
  a matrix application (`apply U`) or a no-op on that register (`classicalNop`).
  Unitarity and the classical tape/address transitions are not part of this interface.
* `compileCircuit` translates a counted circuit gate-by-gate into such a program, sending
  `Step.gate U` to `apply U` and an oracle query to the oracle read `apply oracle`.
* `prop21_compiled_program_runs` proves that executing the compiled program is *exactly* the
  circuit semantics `Run` (same amplitude function, no error term).
* `prop21_time_charge` proves that the compiled program is charged `3 · Size C` (the model
  fixes the positive charge `instrCost = 3` per instruction), a fixed constant factor;
  `prop21_oracleFree_time` sharpens this to `3 · GateCount C` for oracle-free circuits,
  using `gateCount_add_queryCount`.
* `prop21_circuit_to_machine` lifts the compilation to length-indexed circuit families:
  applying the same bounded readout functional to the output of `Run` and `runProgram`
  gives the same score, and the charged time is `3 ·` the circuit size.

## What is *not* formalized

The interface records tape sizes but does not require matrix unitarity or give
tape-transition semantics, a finite gate vocabulary, locality, or a computable uniform
generator.  The equivalence below is
therefore for the instruction-stream model defined here.  It does not establish the
corresponding simulation theorem for a full four-tape machine.
-/

set_option autoImplicit false

open Qatlib.Papers.DihedralHSP13.MainResults.MachineModel
namespace Qatlib.Papers.DihedralHSP13.MainResults.MachineModel

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Operational semantics of one machine instruction on an amplitude function. -/
def machineCircuit (P : List (MachineInstr I)) : Circuit I :=
  P.map fun i => match i with
    | .apply U => Step.gate U
    | .classicalNop => Step.gate 1

/-- The reverse translation preserves the data-register execution exactly. -/
theorem run_machineCirc (P : List (MachineInstr I)) (ψ : QState I) :
    Run 1 (machineCircuit P) ψ = runProgram P ψ := by
  induction P generalizing ψ with
  | nil => rfl
  | cons i P ih =>
    cases i with
    | apply U => simpa [machineCircuit, Run, runProgram, execInstr] using ih (ApplyGate U ψ)
    | classicalNop => simpa [machineCircuit, Run, runProgram, execInstr] using ih ψ

/-- The circuit family obtained by translating each machine instruction to one gate. -/
noncomputable def circuitFamily (M : RamQuantumMachine) : UniformQuantumCircuitFamily where
  width := M.width
  circuit n := machineCircuit (M.program n)
  oracle _ := 1
  initState := M.initState
  acceptProj := M.acceptProj
  zero_one := M.zero_one
  gateCount n := (M.program n).length
  gateCount_spec n := by simp [Size, machineCircuit]

/-
/-- **Instruction-stream instance of Proposition 2.1** (Kuperberg 2013, §2, p. 2).
For the circuit and machine interfaces defined here, both translations preserve bounded
readout scores and multiply cost by at most a fixed constant.  This statement uses the
data-register projection; tape transitions and computable uniformity are not represented. -/
theorem prop21_gate_complexity_equiv_time :
    (∃ c : ℕ, 0 < c ∧ ∀ F : UniformQuantumCircuitFamily,
        ∃ M : RamQuantumMachine, SimulatedBy c F M) ∧
      (∃ c : ℕ, 0 < c ∧ ∀ M : RamQuantumMachine,
        ∃ F : UniformQuantumCircuitFamily, SimulatedByCircuit c M F) := by
  constructor
  · exact ⟨instrCost, by decide, fun F => ⟨compileFamily F, prop21_circuit_to_machine F⟩⟩
  · refine ⟨1, by decide, fun M => ⟨circuitFamily M, ?_, ?_⟩⟩
    · intro n x
      change M.acceptProj n (Run 1 (machineCircuit (M.program n)) (M.initState n x)) =
        M.acceptProj n (runProgram (M.program n) (M.initState n x))
      rw [run_machineCirc]
    · intro n
      change (M.program n).length ≤ 1 * M.time n
      rw [M.time_spec]
      simp only [one_mul, programTime, instrCost]
      omega
 -/

end Qatlib.Papers.DihedralHSP13.MainResults.MachineModel
