/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LocalMachine.LocalTransport.LocalMachine
import Qatlib.Concepts.LocalMachine.LocalTransport.LocalMachineDefs
import Qatlib.Foundations.StandardModel.WindowSim.QtmSimulationDefs
import Qatlib.Concepts.UniformBqp.Phi3Compile.StandardModelDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.LocalMachine.LocalTransport.LocalMachine
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

namespace Qatlib.Papers.QComplexity97.MachineDefs
namespace LocalMachineUniform

inductive NFState where
  | scan
  | back
  | zig
  | zin
  | halt
  deriving DecidableEq, Fintype, Repr

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

def nfSupportOf (v : NFState × FourierSymbol) : List (QtmMove × NFState × FourierSymbol) :=
  nfSupport v.1 v.2

noncomputable def nfValue : NFState → FourierSymbol → QtmMove → NFState → FourierSymbol → ℂ
  | .scan, .bit0, .right, .scan, b => fourierH b .bit0
  | .scan, .bit1, .right, .scan, b => fourierH b .bit1
  | _, _, _, _, _ => 1

noncomputable def nfRule : QtmRule NFState FourierSymbol where
  blank := FourierSymbol.blank
  start := NFState.scan
  step := fun q a d q' b =>
    if (d, q', b) ∈ nfSupport q a then nfValue q a d q' b else 0

def nfDataCell (n c : ℕ) : Prop := 1 ≤ c ∧ c ≤ n

instance nfDataCellDecidable (n c : ℕ) : Decidable (nfDataCell n c) := by
  unfold nfDataCell
  infer_instance

def nfCellClass (n c : ℕ) : FourierSymbol :=
  if nfDataCell n c then FourierSymbol.bit0 else FourierSymbol.blank

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

def nfCtrlRun (n t : ℕ) : NFState × ℕ :=
  match t with
  | 0 => (.scan, 1)
  | t + 1 => nfCtrlStep n (nfCtrlRun n t)

def nfBudget (n : ℕ) : ℕ := 2 * n + 4

end LocalMachineUniform
end Qatlib.Papers.QComplexity97.MachineDefs
