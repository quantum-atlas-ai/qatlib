/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# A clocked oracle stack machine

Defines `Instr`, `State`, and the fuel-bounded execution functions `step` and `run`. Each active
step incurs a tick and unit cost, with an additional address-length charge for an oracle query
recorded in the log.

`scanProgram` supplies a simple input-scanning example, and `addressWork` totals logged
query-address lengths. The computational setting is motivated by standard oracle models; see
[KitaevShenVyalyi2002].

## Main statements

* `Instr`: Instructions for branching on input, consuming input, emitting output, extending the
  query address, querying an oracle slot, and halting.
* `step`: Executes one instruction unless halted, charging one tick and one unit of cost plus
  the address length for a query; an invalid program counter halts with an error.
* `run`: Executes the step function repeatedly for the given natural-number fuel.
* `addressWork`: The total query-address work, defined as the sum of address lengths in the
  query log.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option autoImplicit false
namespace Qatlib.Foundations.ClockedOracle.StackProgram
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-- Instructions for branching on input, consuming input, emitting output, extending the query
address, querying an oracle slot, and halting. -/
inductive Instr where
 | peek (onEnd onFalse onTrue : ℕ)
 | pop (next : ℕ)
 | emit (value : Bool) (next : ℕ)
 | address (value : Bool) (next : ℕ)
 | query (slot onFalse onTrue : ℕ)
 | halt
 deriving DecidableEq, Repr

/-- A machine configuration containing the program counter, input, address and output stacks,
halt and error flags, tick and cost counters, and query log. -/
structure State where
 pc : ℕ := 0
 input : List Bool := []
 address : List Bool := []
 output : List Bool := []
 halted : Bool := false
 error : Bool := false
 ticks : ℕ := 0
 cost : ℕ := 0
 log : List (ℕ×List Bool) := []
 deriving DecidableEq, Repr

/-- The initial configuration with input `xs` and all other fields at their defaults. -/
def init (xs : List Bool) : State := {input:=xs}
/-- Executes one instruction unless halted, charging one tick and one unit of cost plus the
address length for a query; an invalid program counter halts with an error. -/
def step (P : List Instr) (O : ℕ→List Bool→Bool) (s : State) : State :=
 if s.halted then s else
 let t := {s with ticks:=s.ticks+1,cost:=s.cost+1}
 match P[s.pc]? with
 | none => {t with halted:=true,error:=true}
 | some .halt => {t with halted:=true}
 | some (.peek e f r) => {t with pc:=match s.input.head? with | none=>e | some false=>f | some true=>r}
 | some (.pop pc) => {t with pc:=pc,input:=s.input.tail}
 | some (.emit b pc) => {t with pc:=pc,output:=b::s.output}
 | some (.address b pc) => {t with pc:=pc,address:=b::s.address}
 | some (.query slot f r) => {t with pc := (if O slot s.address then r else f), cost := s.cost+1+s.address.length, log := (slot,s.address)::s.log}

/-- Executes the step function repeatedly for the given natural-number fuel. -/
def run (P : List Instr) (O : ℕ→List Bool→Bool) : ℕ→State→State
 | 0,s=>s
 | k+1,s=>run P O k (step P O s)

/-- The four-instruction program that emits a true bit and pops the input for each input bit,
then halts when the input is empty. -/
def scanProgram : List Instr := [.peek 3 1 1,.emit true 2,.pop 0,.halt]
/-- The total query-address work, defined as the sum of address lengths in the query log. -/
def addressWork (s : State) : ℕ := (s.log.map fun p=>p.2.length).sum

end Qatlib.Foundations.ClockedOracle.StackProgram
