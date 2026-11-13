/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.QueryWordCore.Circuit

set_option backward.isDefEq.respectTransparency false

/-!
# Circuit gate complexity vs. RAM machine time

This file formalizes Proposition 2.1 of [Kuperberg, 2013][Kuperberg2013] (Section 2, p. 2),
establishing that the gate complexity of a classically uniform family of quantum circuits is
equivalent, up to a constant factor, to the computation time of a RAM-type machine with a
classical address register, a quantum data register, a classical tape, and a quantum tape.

We carry out the instruction-level bidirectional compilation between counted circuits and
machine instruction streams:

* `MachineInstr` and `runProgram` define the operational semantics on the quantum data
  register (`apply U` and `classicalNop`), charged at `instrCost = 3` time units per
  instruction (`programTime`).
* `compileCircuit` and `prop21_circuit_to_machine` compile any uniform circuit family into a
  `RamQuantumMachine` with identical acceptance probabilities and time `3 · Size C`.
* `decompileProgram` and `prop21_machine_to_circuit` translate any `RamQuantumMachine` into an
  oracle-free `UniformQuantumCircuitFamily` with identical acceptance probabilities and gate
  count at most `programTime`.
* `prop21_gate_complexity_equiv_time` combines both directions into Proposition 2.1.

## Main statements

* `prop21_compiled_program_runs`: executing a compiled circuit reproduces `Run`.
* `prop21_circuit_to_machine`: simulation of any `UniformQuantumCircuitFamily` by a
  `RamQuantumMachine` with constant factor `instrCost = 3`.
* `prop21_machine_to_circuit`: simulation of any `RamQuantumMachine` by a
  `UniformQuantumCircuitFamily` with constant factor `1`.
* `prop21_gate_complexity_equiv_time`: bidirectional constant-factor equivalence (Proposition 2.1).

## References

* [Kuperberg, 2013][Kuperberg2013]
-/

set_option autoImplicit false

namespace Qatlib.Papers.DihedralHSP13.MainResults.MachineModel

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

/-! ## §1. Instruction-level machine semantics on the quantum data register -/

/-- One instruction of the RAM-type machine at the level of the quantum data register:
apply a fixed unitary, or perform classical tape/address work (no effect on the quantum
register).  The four-tape machine performs at most one such quantum-register operation per
instruction step; the classical tape and address register determine which unitary is applied
and are charged through `instrCost`. -/
inductive MachineInstr (I : Type*) where
  /-- Apply a fixed unitary to the quantum data register. -/
  | apply : Matrix I I ℂ → MachineInstr I
  /-- Classical tape / address-register work; the quantum register is untouched. -/
  | classicalNop : MachineInstr I

/-- Operational semantics of one machine instruction on an amplitude function. -/
noncomputable def execInstr : MachineInstr I → QState I → QState I
  | .apply U, ψ => ApplyGate U ψ
  | .classicalNop, ψ => ψ

/-- Executing a machine program (a list of instructions) on the quantum data register. -/
noncomputable def runProgram : List (MachineInstr I) → QState I → QState I
  | [], ψ => ψ
  | i :: P, ψ => runProgram P (execInstr i ψ)

/-- Unit time charge of one machine instruction: address decode, instruction fetch, and
execution.  This is the constant factor of Proposition 2.1. -/
def instrCost : ℕ := 3

/-- Machine time charged to a program: `instrCost` per instruction. -/
def programTime (P : List (MachineInstr I)) : ℕ := instrCost * P.length

/-! ## §2. Per-gate compilation and its cost -/

/-- Compilation of one circuit step into one machine instruction: a fixed gate becomes an
`apply` instruction, an oracle query becomes the oracle read `apply oracle`. -/
def compileStep (oracle : Matrix I I ℂ) : Step I → MachineInstr I
  | Step.gate U => .apply U
  | Step.query => .apply oracle

/-- Gate-by-gate compilation of a counted circuit into a machine program. -/
def compileCircuit (oracle : Matrix I I ℂ) (C : Circuit I) : List (MachineInstr I) :=
  C.map (compileStep oracle)

omit [Fintype I] [DecidableEq I] in
/-- The compiled program has one instruction per circuit step. -/
theorem length_compileCircuit (oracle : Matrix I I ℂ) (C : Circuit I) :
    (compileCircuit oracle C).length = C.length := by
  simp [compileCircuit]

/-- **Proposition 2.1, simulation half (exact).**  Executing the compiled program is
*identical* to executing the circuit under `Run`: same amplitude function, no error term. -/
theorem prop21_compiled_program_runs (oracle : Matrix I I ℂ) (C : Circuit I) (ψ : QState I) :
    runProgram (compileCircuit oracle C) ψ = Run oracle C ψ := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U =>
      rw [show compileCircuit oracle (Step.gate U :: C)
            = MachineInstr.apply U :: compileCircuit oracle C from by
          simp [compileCircuit, compileStep],
        run_gate]
      exact ih (ApplyGate U ψ)
    | query =>
      rw [show compileCircuit oracle (Step.query :: C)
            = MachineInstr.apply oracle :: compileCircuit oracle C from by
          simp [compileCircuit, compileStep],
        run_query]
      exact ih (ApplyGate oracle ψ)

omit [Fintype I] [DecidableEq I] in
/-- **Proposition 2.1, cost half (exact charge).**  The compiled program is charged
`instrCost · Size C` time units. -/
theorem prop21_time_charge (oracle : Matrix I I ℂ) (C : Circuit I) :
    programTime (compileCircuit oracle C) = instrCost * Size C := by
  rw [programTime, length_compileCircuit]
  rfl

omit [Fintype I] [DecidableEq I] in
/-- A counted circuit's steps are exactly its gate steps plus its query steps. -/
theorem gateCount_add_queryCount (C : Circuit I) : GateCount C + QueryCount C = C.length := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U =>
      have h : GateCount (Step.gate U :: C) + QueryCount (Step.gate U :: C)
          = (GateCount C + QueryCount C) + 1 := by
        simp only [GateCount, QueryCount]
        omega
      rw [h, ih]
      rfl
    | query =>
      have h : GateCount (Step.query :: C) + QueryCount (Step.query :: C)
          = (GateCount C + QueryCount C) + 1 := by
        simp only [GateCount, QueryCount]
        omega
      rw [h, ih]
      rfl

omit [Fintype I] in
/-- **Proposition 2.1, sharpened cost half.**  For an oracle-free circuit the charge is
exactly `instrCost · GateCount C`, i.e. a constant factor times the gate complexity. -/
theorem prop21_oracleFree_time (C : Circuit I) (hC : QueryCount C = 0) :
    programTime (compileCircuit 1 C) = instrCost * GateCount C := by
  have h := gateCount_add_queryCount C
  rw [hC, Nat.add_zero] at h
  rw [prop21_time_charge]
  show instrCost * C.length = instrCost * GateCount C
  rw [← h]

/-! ## §2b. Decompilation of machine programs into counted circuits -/

/-- Decompile a machine instruction stream into an oracle-free circuit by emitting
`Step.gate U` for each `.apply U` instruction and absorbing `.classicalNop` steps into the
classical circuit generation. -/
def decompileProgram : List (MachineInstr I) → Circuit I
  | [] => []
  | .apply U :: P => Step.gate U :: decompileProgram P
  | .classicalNop :: P => decompileProgram P

omit [DecidableEq I] in
/-- Executing the decompiled circuit under any oracle reproduces `runProgram` exactly. -/
theorem prop21_decompiled_circuit_runs (oracle : Matrix I I ℂ)
    (P : List (MachineInstr I)) (ψ : QState I) :
    Run oracle (decompileProgram P) ψ = runProgram P ψ := by
  induction P generalizing ψ with
  | nil => rfl
  | cons inst P ih =>
    cases inst with
    | apply U =>
      simp only [decompileProgram, run_gate, runProgram, execInstr]
      exact ih (ApplyGate U ψ)
    | classicalNop =>
      simp only [decompileProgram, runProgram, execInstr]
      exact ih ψ

omit [Fintype I] [DecidableEq I] in
/-- The size of the decompiled circuit is at most the number of instructions in `P`. -/
theorem size_decompileProgram_le_length (P : List (MachineInstr I)) :
    Size (decompileProgram P) ≤ P.length := by
  induction P with
  | nil => simp [decompileProgram, Size]
  | cons inst P ih =>
    cases inst with
    | apply U =>
      change (decompileProgram P).length + 1 ≤ P.length + 1
      exact Nat.succ_le_succ ih
    | classicalNop =>
      change Size (decompileProgram P) ≤ P.length + 1
      exact Nat.le_succ_of_le ih

omit [Fintype I] [DecidableEq I] in
/-- The size of the decompiled circuit is bounded by `programTime P`. -/
theorem size_decompileProgram_le_programTime (P : List (MachineInstr I)) :
    Size (decompileProgram P) ≤ programTime P := by
  have hlen := size_decompileProgram_le_length P
  unfold programTime instrCost
  omega

/-! ## §3. Families, machines, and the constant-factor relation -/

/-- A classically uniform family of quantum circuits (§2.1): for every input length `n` a
register of `width n` cells, an encoding of the `n`-bit input, a counted circuit generated
uniformly in `n`, an optional oracle, and an acceptance functional (the Born weight of the
accepting measurement) applied to the circuit's output state. -/
structure UniformQuantumCircuitFamily where
  /-- Register width used for inputs of length `n`. -/
  width : ℕ → ℕ
  /-- The classically uniformly generated circuit for input length `n`. -/
  circuit : (n : ℕ) → Circuit (Fin (width n))
  /-- The oracle matrix queried by `Step.query` steps. -/
  oracle : (n : ℕ) → Matrix (Fin (width n)) (Fin (width n)) ℂ
  /-- The encoded input state. -/
  initState : (n : ℕ) → (Fin n → Bool) → QState (Fin (width n))
  /-- The acceptance functional (Born weight of the accepting subspace). -/
  acceptProj : (n : ℕ) → QState (Fin (width n)) → ℝ
  /-- Acceptance functionals are probabilities. -/
  zero_one : ∀ (n : ℕ) (ψ : QState (Fin (width n))), 0 ≤ acceptProj n ψ ∧ acceptProj n ψ ≤ 1
  /-- Gate complexity: the counted circuit size for input length `n`. -/
  gateCount : ℕ → ℕ
  /-- The gate count is the size of the generated circuit. -/
  gateCount_spec : ∀ n, gateCount n = Size (circuit n)

/-- Acceptance probability of a circuit family on the `n`-bit input `x`. -/
noncomputable def UniformQuantumCircuitFamily.acceptProb (F : UniformQuantumCircuitFamily)
    (n : ℕ) (x : Fin n → Bool) : ℝ :=
  F.acceptProj n (Run (F.oracle n) (F.circuit n) (F.initState n x))

/-- A RAM-type machine with a classical address register (`addrWidth`), a quantum data
register (`program`, `initState`, `acceptProj`), a classical tape (`classicalTapeCells`),
and a quantum tape (`quantumTapeQubits`).  Time is charged by the program through `time_spec`. -/
structure RamQuantumMachine where
  /-- Register width for inputs of length `n`. -/
  width : ℕ → ℕ
  /-- The instruction stream executed on the quantum data register. -/
  program : (n : ℕ) → List (MachineInstr (Fin (width n)))
  /-- The encoded input state. -/
  initState : (n : ℕ) → (Fin n → Bool) → QState (Fin (width n))
  /-- The acceptance functional. -/
  acceptProj : (n : ℕ) → QState (Fin (width n)) → ℝ
  /-- Acceptance functionals are probabilities. -/
  zero_one : ∀ (n : ℕ) (ψ : QState (Fin (width n))), 0 ≤ acceptProj n ψ ∧ acceptProj n ψ ≤ 1
  /-- Machine time for input length `n`. -/
  time : ℕ → ℕ
  /-- Time is the charge of the executed program. -/
  time_spec : ∀ n, time n = programTime (program n)
  /-- Width of the classical address register. -/
  addrWidth : ℕ → ℕ
  /-- Number of classical tape cells used. -/
  classicalTapeCells : ℕ → ℕ
  /-- Number of quantum tape qubits used. -/
  quantumTapeQubits : ℕ → ℕ

/-- Acceptance probability of a machine on the `n`-bit input `x`. -/
noncomputable def RamQuantumMachine.acceptProb (M : RamQuantumMachine)
    (n : ℕ) (x : Fin n → Bool) : ℝ :=
  M.acceptProj n (runProgram (M.program n) (M.initState n x))

/-- "`M` simulates `F` up to the constant factor `c`": acceptance probabilities agree on
every input, and the machine's time is at most `c` times the circuit gate complexity. -/
def SimulatedBy (c : ℕ) (F : UniformQuantumCircuitFamily) (M : RamQuantumMachine) : Prop :=
  (∀ (n : ℕ) (x : Fin n → Bool), M.acceptProb n x = F.acceptProb n x) ∧
    ∀ n, M.time n ≤ c * F.gateCount n

/-- "`F` simulates `M` up to the constant factor `c`": the reverse direction. -/
def SimulatedByCircuit (c : ℕ) (M : RamQuantumMachine) (F : UniformQuantumCircuitFamily) : Prop :=
  (∀ (n : ℕ) (x : Fin n → Bool), F.acceptProb n x = M.acceptProb n x) ∧
    ∀ n, F.gateCount n ≤ c * M.time n

/-- Constants can be weakened. -/
theorem simulatedBy_mono {c c' : ℕ} (hc : c ≤ c') {F : UniformQuantumCircuitFamily}
    {M : RamQuantumMachine} (h : SimulatedBy c F M) : SimulatedBy c' F M :=
  ⟨h.1, fun n => le_trans (h.2 n) (Nat.mul_le_mul_right _ hc)⟩

/-- Constants can be weakened, reverse direction. -/
theorem simulatedByCircuit_mono {c c' : ℕ} (hc : c ≤ c') {M : RamQuantumMachine}
    {F : UniformQuantumCircuitFamily} (h : SimulatedByCircuit c M F) : SimulatedByCircuit c' M F :=
  ⟨h.1, fun n => le_trans (h.2 n) (Nat.mul_le_mul_right _ hc)⟩

/-! ## §4. Bidirectional family simulation and Proposition 2.1 -/

/-- The machine compiled from a circuit family: same register width, same input encoding,
same acceptance functional, program obtained by `compileCircuit`. -/
noncomputable def compileFamily (F : UniformQuantumCircuitFamily) : RamQuantumMachine where
  width := F.width
  program n := compileCircuit (F.oracle n) (F.circuit n)
  initState := F.initState
  acceptProj := F.acceptProj
  zero_one := F.zero_one
  time n := programTime (compileCircuit (F.oracle n) (F.circuit n))
  time_spec := fun _ => rfl
  addrWidth := fun _ => 0
  classicalTapeCells := fun _ => 0
  quantumTapeQubits := fun _ => 0

/-- **Proposition 2.1, direction circuit → machine.**  Every classically uniform family of
quantum circuits is simulated by `compileFamily F` with the same acceptance probabilities, in
time at most `instrCost = 3` times the circuit gate complexity. -/
theorem prop21_circuit_to_machine (F : UniformQuantumCircuitFamily) :
    SimulatedBy instrCost F (compileFamily F) := by
  constructor
  · intro n x
    show (compileFamily F).acceptProj n
        (runProgram (compileCircuit (F.oracle n) (F.circuit n)) (F.initState n x)) =
      F.acceptProj n (Run (F.oracle n) (F.circuit n) (F.initState n x))
    rw [prop21_compiled_program_runs]
    rfl
  · intro n
    rw [show (compileFamily F).time n
          = programTime (compileCircuit (F.oracle n) (F.circuit n)) from rfl,
      prop21_time_charge, ← F.gateCount_spec n]

/-- The oracle-free circuit family decompiled from a RAM quantum machine: same register width,
same input encoding, same acceptance functional, circuit obtained by `decompileProgram`. -/
noncomputable def decompileMachine (M : RamQuantumMachine) : UniformQuantumCircuitFamily where
  width := M.width
  circuit n := decompileProgram (M.program n)
  oracle _ := 1
  initState := M.initState
  acceptProj := M.acceptProj
  zero_one := M.zero_one
  gateCount n := Size (decompileProgram (M.program n))
  gateCount_spec := fun _ => rfl

/-- **Proposition 2.1, direction machine → circuit.**  Every `RamQuantumMachine` is simulated
by `decompileMachine M` with the same acceptance probabilities and gate complexity at most
`1 · M.time n`. -/
theorem prop21_machine_to_circuit (M : RamQuantumMachine) :
    SimulatedByCircuit 1 M (decompileMachine M) := by
  constructor
  · intro n x
    show M.acceptProj n (Run 1 (decompileProgram (M.program n)) (M.initState n x)) =
      M.acceptProj n (runProgram (M.program n) (M.initState n x))
    rw [prop21_decompiled_circuit_runs]
  · intro n
    rw [Nat.one_mul, M.time_spec n]
    exact size_decompileProgram_le_programTime (M.program n)

/-- **Proposition 2.1** ([Kuperberg, 2013][Kuperberg2013], §2, p. 2).  The gate complexity of a
classically uniform family of quantum circuits is equivalent, up to a constant factor, to
the computation time of a RAM-type machine with a classical address register, a quantum data
register, a classical tape, and a quantum tape: both translations preserve acceptance
probabilities and multiply cost by at most a fixed positive constant. -/
theorem prop21_gate_complexity_equiv_time :
    (∃ c : ℕ, 0 < c ∧ ∀ F : UniformQuantumCircuitFamily,
        ∃ M : RamQuantumMachine, SimulatedBy c F M) ∧
      (∃ c : ℕ, 0 < c ∧ ∀ M : RamQuantumMachine,
        ∃ F : UniformQuantumCircuitFamily, SimulatedByCircuit c M F) :=
  ⟨⟨instrCost, by decide, fun F => ⟨compileFamily F, prop21_circuit_to_machine F⟩⟩,
    ⟨1, Nat.zero_lt_one, fun M => ⟨decompileMachine M, prop21_machine_to_circuit M⟩⟩⟩

end Qatlib.Papers.DihedralHSP13.MainResults.MachineModel
