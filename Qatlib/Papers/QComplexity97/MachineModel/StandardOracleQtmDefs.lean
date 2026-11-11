/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.Phi3Compile.NativeModelFixedGate
import Qatlib.Concepts.UniformBqp.Phi3Compile.NativeModelFixedGateDefs
import Qatlib.Foundations.StandardModel.WindowSim.QtmSimulationDefs
import Qatlib.Foundations.ClockedOracle.StackProgram.ClockedOracleStack
import Qatlib.Foundations.ClockedOracle.StackProgram.ClockedOracleStackDefs
import Qatlib.Concepts.UniformBqp.Phi3Compile.StandardModelDefs

/-!
# Oracle transition supports and billing definitions

The module defines a finite symbol alphabet, control states, and deterministic transition
supports for an explicit oracle-machine example. `oracleMachineStep` assigns amplitude one on
these supports and zero elsewhere.

`OracleCharge` records a request and its access list. The associated fee and bill functions use
the sum of the input, label, and record tariffs, providing the accounting definitions for the
local oracle construction. See [BernsteinVazirani1997].

## Main statements

* `oracleMachineStep`: turns the support table into transition amplitudes.
* `oracleCharge`: records the three access types for a request.
* `oracleBillRepeat`: defines the bill for repeated charges.

## References

* [Bernstein and Vazirani, 1997][BernsteinVazirani1997]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Concepts.UniformBqp.Phi3Compile

set_option autoImplicit false

namespace Qatlib.Papers.QComplexity97.MachineDefs
namespace StandardOracleQtm

/-- The finite tape alphabet consisting of binary symbols `bit0` and `bit1` together with
`blank`. -/
inductive OracleSymbol where
  | bit0
  | bit1
  | blank
  deriving DecidableEq, Fintype, Repr

/-- The four control states `read`, `ask`, `end`, and `halt` of the explicit oracle-machine
example. -/
inductive OracleState where
  | read
  | ask
  | end
  | halt
  deriving DecidableEq, Fintype, Repr

/-- The singleton right-moving transition-support list for each source state-symbol pair,
preserving the scanned symbol. -/
def oracleSupport : OracleState → OracleSymbol → List (QtmMove × OracleState × OracleSymbol)
  | .read, .bit0 => [(.right, .ask, .bit0)]
  | .read, .bit1 => [(.right, .ask, .bit1)]
  | .read, .blank => [(.right, .ask, .blank)]
  | .ask, .bit0 => [(.right, .read, .bit0)]
  | .ask, .bit1 => [(.right, .read, .bit1)]
  | .ask, .blank => [(.right, .end, .blank)]
  | .end, .bit0 => [(.right, .halt, .bit0)]
  | .end, .bit1 => [(.right, .halt, .bit1)]
  | .end, .blank => [(.right, .halt, .blank)]
  | .halt, .bit0 => [(.right, .end, .bit0)]
  | .halt, .bit1 => [(.right, .end, .bit1)]
  | .halt, .blank => [(.right, .read, .blank)]

/-- The transition-support list evaluated at a source state-symbol pair. -/
def oracleSupportOf (v : OracleState × OracleSymbol) : List (QtmMove × OracleState × OracleSymbol) :=
  oracleSupport v.1 v.2

/-- The complex amplitude one on a slot in `oracleSupport q a`, and zero on every other slot. -/
noncomputable def oracleMachineStep (q : OracleState) (a : OracleSymbol) (d : QtmMove)
    (q' : OracleState) (b : OracleSymbol) : ℂ :=
  if (d, q', b) ∈ oracleSupport q a then 1 else 0

/-- A record containing an oracle request and a list of the access types assigned to it. -/
structure OracleCharge (Q A : Type*) where

  request : OracleRequest Q A

  accesses : List OracleAccess
  deriving DecidableEq

/-- The charge record for a request, with access list `inputAccess`, `labelCompare`, and
`recordAccess`. -/
def oracleCharge {Q A : Type*} (r : OracleRequest Q A) : OracleCharge Q A :=
  ⟨r, [.inputAccess, .labelCompare, .recordAccess]⟩

/-- The fixed sum of the input, label, and record fees in tariff `t` for a charge. -/
def OracleCharge.fee {Q A : Type*} (t : OracleTariff) (c : OracleCharge Q A) : ℝ :=
  t.inputFee + t.labelFee + t.recordFee

/-- The sum of the fees of a list of oracle charges. -/
def oracleBill {Q A : Type*} (t : OracleTariff) (cs : List (OracleCharge Q A)) : ℝ :=
  (cs.map (fun c => c.fee t)).sum

/-- The bill `k * c.fee t` for repeating a charge `k` times. -/
def oracleBillRepeat {Q A : Type*} (t : OracleTariff) (c : OracleCharge Q A) (k : ℕ) : ℝ :=
  k * c.fee t

/-- The Boolean test that every transition slot in the first source pair's support is absent
from the second source pair's support. -/
def oracleDisjointCheck (v1 v2 : OracleState × OracleSymbol) : Bool :=
  (oracleSupportOf v1).all (fun slot => !(oracleSupportOf v2).contains slot)

end StandardOracleQtm
end Qatlib.Papers.QComplexity97.MachineDefs
