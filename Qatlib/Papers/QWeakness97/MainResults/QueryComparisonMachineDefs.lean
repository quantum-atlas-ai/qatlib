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

/-!
# Finite oracle machine programs

`MachineProgram` bundles a finite Boolean oracle circuit, an initial state, and an accepting set
of basis configurations. Its state space consists of an address register `Fin n`, a Boolean
answer register, and a workspace `W`; unitary evolution and normalization are separate
properties rather than fields of the structure.

`MachineProgram.queryCount`, `MachineProgram.gateCount`, and `MachineProgram.successProb` expose
the resource counts and acceptance probability used by the finite-circuit constructions
accompanying the amplification discussion of [BennettEtAl1997].

## Main statements

* `MachineProgram` specifies the circuit, initial amplitudes, and accepting configurations.
* `MachineProgram.queryCount` and `MachineProgram.gateCount` count oracle queries and explicit
  matrix gates separately.
* `MachineProgram.successProb` evaluates the accepting-set probability after execution with a
  supplied Boolean oracle.

## References

* [Bennett et al., 1997][BennettEtAl1997]
-/

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

/-- A finite oracle program consisting of a circuit on an address register, a Boolean answer
register, and workspace, together with an initial state and an accepting set. The structure
itself imposes no normalization or unitarity conditions. -/
structure MachineProgram (n : ℕ) (W : Type) where
  circuit : Circuit ((Fin n × Bool) × W)
  initial : QState ((Fin n × Bool) × W)
  accept : Finset ((Fin n × Bool) × W)

/-- The number of oracle-query instructions in the program's circuit. -/
def MachineProgram.queryCount (P : MachineProgram n W) : ℕ := QueryCount P.circuit

/-- The number of explicit matrix-gate instructions in the program's circuit, excluding oracle
queries. -/
def MachineProgram.gateCount (P : MachineProgram n W) : ℕ := GateCount P.circuit

/-- The Born probability of the program's accepting configurations after running its circuit
from the stored initial state with Boolean oracle `g` acting on the address and answer
registers and identity on the workspace. -/
noncomputable def MachineProgram.successProb (P : MachineProgram n W) (g : Fin n → Bool) : ℝ :=
  MeasureProb (Run (TensorGate (BitOracleOn g) (1 : Matrix W W ℂ)) P.circuit P.initial) P.accept

end Qatlib.Papers.QWeakness97.MainResults
