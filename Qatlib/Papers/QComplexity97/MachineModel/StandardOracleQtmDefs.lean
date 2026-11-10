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
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Concepts.UniformBqp.Phi3Compile

set_option autoImplicit false

namespace Qatlib.Papers.QComplexity97.MachineDefs
namespace StandardOracleQtm

inductive OracleSymbol where
  | bit0
  | bit1
  | blank
  deriving DecidableEq, Fintype, Repr

inductive OracleState where
  | read
  | ask
  | end
  | halt
  deriving DecidableEq, Fintype, Repr

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

def oracleSupportOf (v : OracleState × OracleSymbol) : List (QtmMove × OracleState × OracleSymbol) :=
  oracleSupport v.1 v.2

noncomputable def oracleMachineStep (q : OracleState) (a : OracleSymbol) (d : QtmMove)
    (q' : OracleState) (b : OracleSymbol) : ℂ :=
  if (d, q', b) ∈ oracleSupport q a then 1 else 0

structure OracleCharge (Q A : Type*) where

  request : OracleRequest Q A

  accesses : List OracleAccess
  deriving DecidableEq

def oracleCharge {Q A : Type*} (r : OracleRequest Q A) : OracleCharge Q A :=
  ⟨r, [.inputAccess, .labelCompare, .recordAccess]⟩

def OracleCharge.fee {Q A : Type*} (t : OracleTariff) (c : OracleCharge Q A) : ℝ :=
  t.inputFee + t.labelFee + t.recordFee

def oracleBill {Q A : Type*} (t : OracleTariff) (cs : List (OracleCharge Q A)) : ℝ :=
  (cs.map (fun c => c.fee t)).sum

def oracleBillRepeat {Q A : Type*} (t : OracleTariff) (c : OracleCharge Q A) (k : ℕ) : ℝ :=
  k * c.fee t

def oracleDisjointCheck (v1 v2 : OracleState × OracleSymbol) : Bool :=
  (oracleSupportOf v1).all (fun slot => !(oracleSupportOf v2).contains slot)

end StandardOracleQtm
end Qatlib.Papers.QComplexity97.MachineDefs
