/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs

open Turing
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Bits)
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks

def setTwo (S : Slot → Bits) (src dst : Slot) (xs ys : Bits) : Slot → Bits :=
  Function.update (Function.update S src xs) dst ys

@[simp] theorem setTwo_src (S : Slot → Bits) (src dst : Slot) (xs ys : Bits) (h : src ≠ dst) :
    setTwo S src dst xs ys src = xs := by simp [setTwo,h]

@[simp] theorem setTwo_dst (S : Slot → Bits) (src dst : Slot) (xs ys : Bits) :
    setTwo S src dst xs ys dst = ys := by simp [setTwo]

theorem setTwo_updates (S : Slot → Bits) (src dst : Slot) (xs ys us vs : Bits) :
    Function.update (Function.update (setTwo S src dst xs ys) src us) dst vs =
      setTwo S src dst us vs := by
  funext i
  by_cases hd : i=dst <;> by_cases hs : i=src <;> simp [setTwo,Function.update_apply,hd,hs]

@[simp] theorem setTwo_update_src (S : Slot → Bits) (src dst : Slot) (xs ys us : Bits)
    (h : src ≠ dst) : Function.update (setTwo S src dst xs ys) src us = setTwo S src dst us ys := by
  funext i
  by_cases hd : i=dst <;> by_cases hs : i=src <;> simp [setTwo,Function.update_apply,hd,hs] <;> simp_all

@[simp] theorem setTwo_update_dst (S : Slot → Bits) (src dst : Slot) (xs ys us : Bits) :
    Function.update (setTwo S src dst xs ys) dst us = setTwo S src dst xs us := by
  simp [setTwo]

@[simp] theorem clear_load (v : Local) (o : Option Bool) : (v.load o).clear = v.clear := rfl

@[simp] theorem clear_clear (v : Local) : v.clear.clear = v.clear := rfl

@[simp] theorem load_clear_none (v : Local) : v.clear.load none = v.load none := rfl

@[simp] theorem load_read (v : Local) (o : Option Bool) : (v.load o).read = o := rfl

def moveStmt (src dst : Slot) (again : Label)
    (done : TM2.Stmt (fun _ : Slot => Bool) Label Local) :
    TM2.Stmt (fun _ : Slot => Bool) Label Local :=
  .pop src Local.load (.branch (fun v => v.read.isSome)
    (.push dst (fun v => v.read.getD false) (.load Local.clear (.goto (fun _ => again)))) done)

theorem move_run (src dst : Slot) (again : Label)
    (done : TM2.Stmt (fun _ : Slot => Bool) Label Local)
    (hcode : program again = moveStmt src dst again done) (hne : src ≠ dst)
    (xs ys : Bits) (S : Slot → Bits) (v : Local) :
    stackRun program (xs.length+1) ⟨some again,v,setTwo S src dst xs ys⟩ =
      some (TM2.stepAux done (v.load none) (setTwo S src dst [] (xs.reverse++ys))) := by
  induction xs generalizing ys v with
  | nil => simp [stackRun,TM2.step,hcode,moveStmt,TM2.stepAux,hne]
  | cons b bs ih =>
      have hs : TM2.step program ⟨some again,v,setTwo S src dst (b::bs) ys⟩ =
          some ⟨some again,v.clear,setTwo S src dst bs (b::ys)⟩ := by
        simp [TM2.step,hcode,moveStmt,TM2.stepAux,hne,Ne.symm hne,Local.load,Local.clear]
      rw [List.length_cons,stackRun,hs,Option.bind_some,ih]
      simp [List.reverse_cons,List.append_assoc]

def bitPair (swapped b : Bool) : Bits := if swapped then [b,true] else [true,b]

def pairStmt (src dst : Slot) (again : Label) (swapped : Bool)
    (done : TM2.Stmt (fun _ : Slot => Bool) Label Local) :
    TM2.Stmt (fun _ : Slot => Bool) Label Local :=
  .pop src Local.load (.branch (fun v => v.read.isSome)
    (.push dst (fun v => if swapped then true else v.read.getD false)
      (.push dst (fun v => if swapped then v.read.getD false else true)
        (.load Local.clear (.goto (fun _ => again))))) done)

theorem pair_run (src dst : Slot) (again : Label) (swapped : Bool)
    (done : TM2.Stmt (fun _ : Slot => Bool) Label Local)
    (hcode : program again = pairStmt src dst again swapped done) (hne : src ≠ dst)
    (xs ys : Bits) (S : Slot → Bits) (v : Local) :
    stackRun program (xs.length+1) ⟨some again,v,setTwo S src dst xs ys⟩ =
      some (TM2.stepAux done (v.load none)
        (setTwo S src dst [] (xs.reverse.flatMap (bitPair swapped)++ys))) := by
  induction xs generalizing ys v with
  | nil => simp [stackRun,TM2.step,hcode,pairStmt,TM2.stepAux,hne]
  | cons b bs ih =>
      have hs : TM2.step program ⟨some again,v,setTwo S src dst (b::bs) ys⟩ =
          some ⟨some again,v.clear,setTwo S src dst bs (bitPair swapped b++ys)⟩ := by
        cases swapped <;> simp [TM2.step,hcode,pairStmt,TM2.stepAux,hne,Ne.symm hne,
          bitPair,Local.load,Local.clear]
      rw [List.length_cons,stackRun,hs,Option.bind_some,ih]
      simp [List.reverse_cons,List.flatMap_append,List.append_assoc]

end Qatlib.Concepts.QueryComplexity.DegreeMethod
