/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LocalMachine.LocalTransport.LocalMachine
import Qatlib.Concepts.LocalMachine.LocalTransport.LocalMachineDefs
import Qatlib.Foundations.StandardModel.WindowSim.QtmSimulationDefs
import Qatlib.Concepts.UniformBqp.Phi3Compile.StandardModelDefs

/-!
# Normal-form scan rules and control trace definitions

`NFState`, `nfSupport`, and `nfValue` define a scan rule with Hadamard amplitudes on binary
symbols and deterministic return and final moves. `nfRule` restricts these values to the listed
transition supports.

The module also defines an abstract control trace over a block of data cells and the budget
`nfBudget n = 2 * n + 4`, used to state the exact scan schedule. See [BernsteinVazirani1997].

## Main statements

* `nfRule`: assembles the supported transition rule.
* `nfCtrlRun`: iterates the abstract state and cell transition.
* `nfBudget`: specifies the exact control budget.

## References

* [Bernstein and Vazirani, 1997][BernsteinVazirani1997]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.LocalMachine.LocalTransport.LocalMachine
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

namespace Qatlib.Papers.QComplexity97.MachineDefs
namespace LocalMachineUniform

/-- The five control states `scan`, `back`, `zig`, `zin`, and `halt` of the normal-form scan
rule. -/
inductive NFState where
  | scan
  | back
  | zig
  | zin
  | halt
  deriving DecidableEq, Fintype, Repr

/-- The move and next-state table for the normal-form scan rule on each control state and tape
symbol. -/
def nfMoveNext : NFState → FourierSymbol → QtmMove × NFState
  | .scan, .bit0 => (.right, .scan)
  | .scan, .bit1 => (.right, .scan)
  | .scan, .blank => (.left, .back)
  | .back, .bit0 => (.left, .back)
  | .back, .bit1 => (.left, .back)
  | .back, .blank => (.right, .zig)
  | .zig, .bit0 => (.right, .zin)
  | .zig, .bit1 => (.right, .zin)
  | .zig, .blank => (.right, .zin)
  | .zin, .bit0 => (.left, .halt)
  | .zin, .bit1 => (.left, .halt)
  | .zin, .blank => (.left, .halt)
  | .halt, .bit0 => (.right, .zig)
  | .halt, .bit1 => (.right, .zig)
  | .halt, .blank => (.right, .scan)

/-- The finite transition-support list for each source state-symbol pair, with two binary
outputs on binary scan rows. -/
def nfSupport : NFState → FourierSymbol → List (QtmMove × NFState × FourierSymbol)
  | .scan, .bit0 => [(.right, .scan, .bit0), (.right, .scan, .bit1)]
  | .scan, .bit1 => [(.right, .scan, .bit0), (.right, .scan, .bit1)]
  | .scan, .blank => [(.left, .back, .blank)]
  | .back, .bit0 => [(.left, .back, .bit0)]
  | .back, .bit1 => [(.left, .back, .bit1)]
  | .back, .blank => [(.right, .zig, .blank)]
  | .zig, .bit0 => [(.right, .zin, .bit0)]
  | .zig, .bit1 => [(.right, .zin, .bit1)]
  | .zig, .blank => [(.right, .zin, .blank)]
  | .zin, .bit0 => [(.left, .halt, .bit0)]
  | .zin, .bit1 => [(.left, .halt, .bit1)]
  | .zin, .blank => [(.left, .halt, .blank)]
  | .halt, .bit0 => [(.right, .zig, .bit0)]
  | .halt, .bit1 => [(.right, .zig, .bit1)]
  | .halt, .blank => [(.right, .scan, .blank)]

/-- The transition-support list at a source state-symbol pair. -/
def nfSupportOf (v : NFState × FourierSymbol) : List (QtmMove × NFState × FourierSymbol) :=
  nfSupport v.1 v.2

/-- The Hadamard entry on binary scan transitions, and one on all other transition arguments
before support restriction. -/
noncomputable def nfValue : NFState → FourierSymbol → QtmMove → NFState → FourierSymbol → ℂ
  | .scan, .bit0, .right, .scan, b => fourierH b .bit0
  | .scan, .bit1, .right, .scan, b => fourierH b .bit1
  | _, _, _, _, _ => 1

/-- The QTM rule with start state `scan` and blank symbol `blank`, with amplitudes `nfValue` on
`nfSupport` and zero elsewhere. -/
noncomputable def nfRule : QtmRule NFState FourierSymbol where
  blank := FourierSymbol.blank
  start := NFState.scan
  step := fun q a d q' b =>
    if (d, q', b) ∈ nfSupport q a then nfValue q a d q' b else 0

/-- The cell index lies between one and `n`, inclusive. -/
def nfDataCell (n c : ℕ) : Prop := 1 ≤ c ∧ c ≤ n

instance nfDataCellDecidable (n c : ℕ) : Decidable (nfDataCell n c) := by
  unfold nfDataCell
  infer_instance

/-- The symbol `bit0` on data cells and `blank` outside the data block. -/
def nfCellClass (n c : ℕ) : FourierSymbol :=
  if nfDataCell n c then FourierSymbol.bit0 else FourierSymbol.blank

/-- The deterministic state and natural-number cell update obtained from the normal-form scan
table and `nfCellClass`. -/
def nfCtrlStep (n : ℕ) (qc : NFState × ℕ) : NFState × ℕ :=
  match qc with
  | (q, c) =>
    match q, nfCellClass n c with
    | .scan, .bit0 => (.scan, c + 1)
    | .scan, .bit1 => (.scan, c + 1)
    | .scan, .blank => (.back, c - 1)
    | .back, .bit0 => (.back, c - 1)
    | .back, .bit1 => (.back, c - 1)
    | .back, .blank => (.zig, c + 1)
    | .zig, .bit0 => (.zin, c + 1)
    | .zig, .bit1 => (.zin, c + 1)
    | .zig, .blank => (.zin, c + 1)
    | .zin, .bit0 => (.halt, c - 1)
    | .zin, .bit1 => (.halt, c - 1)
    | .zin, .blank => (.halt, c - 1)
    | .halt, .bit0 => (.zig, c + 1)
    | .halt, .bit1 => (.zig, c + 1)
    | .halt, .blank => (.scan, c + 1)

/-- The iterated control trace beginning in state `scan` at cell one. -/
def nfCtrlRun (n t : ℕ) : NFState × ℕ :=
  match t with
  | 0 => (.scan, 1)
  | t + 1 => nfCtrlStep n (nfCtrlRun n t)

/-- The control-step budget `2 * n + 4`. -/
def nfBudget (n : ℕ) : ℕ := 2 * n + 4

end LocalMachineUniform
end Qatlib.Papers.QComplexity97.MachineDefs
