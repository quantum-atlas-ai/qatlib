/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryModelComparisonDefs
import Qatlib.Concepts.UniformBqp.OracleAmplify.StandardOracleSequentialCopiesStat
import Qatlib.Concepts.UniformBqp.OracleAmplify.StandardOracleTidyAmplificationStat
import Qatlib.Concepts.UniformBqp.OracleAmplify.StandardOracleSequentialCopiesStre
import Qatlib.Concepts.UniformBqp.OracleAmplify.StandardOracleTidyAmplificationStre
import Mathlib.Tactic.Linarith
set_option warningAsError false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.UniformBqp.OracleAmplify
open Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Qatlib.Papers.QWeakness97.MainResults

open Matrix
open Qatlib
open scoped Classical BigOperators ENNReal

variable (n : ℕ) {W : Type} [Fintype W] [DecidableEq W]

structure MachineProgram (n : ℕ) (W : Type) where
  circuit : Circuit ((Fin n × Bool) × W)
  initial : QState ((Fin n × Bool) × W)
  accept : Finset ((Fin n × Bool) × W)

def MachineProgram.queryCount (P : MachineProgram n W) : ℕ := QueryCount P.circuit

def MachineProgram.gateCount (P : MachineProgram n W) : ℕ := GateCount P.circuit

noncomputable def MachineProgram.successProb (P : MachineProgram n W) (g : Fin n → Bool) : ℝ :=
  MeasureProb (Run (TensorGate (BitOracleOn g) (1 : Matrix W W ℂ)) P.circuit P.initial) P.accept

end Qatlib.Papers.QWeakness97.MainResults
