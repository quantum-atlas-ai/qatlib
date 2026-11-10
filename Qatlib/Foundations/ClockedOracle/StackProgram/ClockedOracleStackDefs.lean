/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

set_option autoImplicit false
namespace Qatlib.Foundations.ClockedOracle.StackProgram
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

inductive Instr where
 | peek (onEnd onFalse onTrue : ℕ)
 | pop (next : ℕ)
 | emit (value : Bool) (next : ℕ)
 | address (value : Bool) (next : ℕ)
 | query (slot onFalse onTrue : ℕ)
 | halt
 deriving DecidableEq, Repr

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

def init (xs : List Bool) : State := {input:=xs}
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

def run (P : List Instr) (O : ℕ→List Bool→Bool) : ℕ→State→State
 | 0,s=>s
 | k+1,s=>run P O k (step P O s)

def scanProgram : List Instr := [.peek 3 1 1,.emit true 2,.pop 0,.halt]
def addressWork (s : State) : ℕ := (s.log.map fun p=>p.2.length).sum

end Qatlib.Foundations.ClockedOracle.StackProgram
