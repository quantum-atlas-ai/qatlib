/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs

/-!
# Stack transfers for rational division

This module defines a helper for updating two stacks and verifies loops that transfer bits,
either directly or as marker and payload pairs. The theorems `move_run` and `pair_run` give
exact step counts, reversed source order on the destination, and execution of the supplied
continuation. These routines use the finite machine setting described in [KitaevShenVyalyi2002].

## Main statements

* `setTwo`: updates the source stack and then the destination stack.
* `move_run`: transfers an entire word in reverse order.
* `pair_run`: transfers a word using `bitPair` for each bit.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs

open Turing
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Bits)
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks

/-- Updates stack `src` to `xs` and then stack `dst` to `ys`, so the destination update takes
precedence when the indices coincide. -/
def setTwo (S : Slot → Bits) (src dst : Slot) (xs ys : Bits) : Slot → Bits :=
  Function.update (Function.update S src xs) dst ys

/-- For distinct source and destination indices, the source stack of `setTwo` is `xs`. -/
@[simp] theorem setTwo_src (S : Slot → Bits) (src dst : Slot) (xs ys : Bits) (h : src ≠ dst) :
    setTwo S src dst xs ys src = xs := by simp [setTwo,h]

/-- The destination stack of `setTwo` is `ys`. -/
@[simp] theorem setTwo_dst (S : Slot → Bits) (src dst : Slot) (xs ys : Bits) :
    setTwo S src dst xs ys dst = ys := by simp [setTwo]

/-- Updating both designated stacks of `setTwo` in source then destination order replaces the
two stored words. -/
theorem setTwo_updates (S : Slot → Bits) (src dst : Slot) (xs ys us vs : Bits) :
    Function.update (Function.update (setTwo S src dst xs ys) src us) dst vs =
      setTwo S src dst us vs := by
  funext i
  by_cases hd : i=dst <;> by_cases hs : i=src <;> simp [setTwo,Function.update_apply,hd,hs]

/-- For distinct indices, updating the source stack of `setTwo` replaces only its source word. -/
@[simp] theorem setTwo_update_src (S : Slot → Bits) (src dst : Slot) (xs ys us : Bits)
    (h : src ≠ dst) : Function.update (setTwo S src dst xs ys) src us = setTwo S src dst us ys := by
  funext i
  by_cases hd : i=dst <;> by_cases hs : i=src <;> simp [setTwo,Function.update_apply,hd,hs] <;> simp_all

/-- Updating the destination stack of `setTwo` replaces its destination word. -/
@[simp] theorem setTwo_update_dst (S : Slot → Bits) (src dst : Slot) (xs ys us : Bits) :
    Function.update (setTwo S src dst xs ys) dst us = setTwo S src dst xs us := by
  simp [setTwo]

/-- Loading a read symbol and then clearing it agrees with clearing the original state. -/
@[simp] theorem clear_load (v : Local) (o : Option Bool) : (v.load o).clear = v.clear := rfl

/-- Clearing the read symbol is idempotent. -/
@[simp] theorem clear_clear (v : Local) : v.clear.clear = v.clear := rfl

/-- Clearing the state before loading `none` has no additional effect. -/
@[simp] theorem load_clear_none (v : Local) : v.clear.load none = v.load none := rfl

/-- The read field after `load o` is `o`. -/
@[simp] theorem load_read (v : Local) (o : Option Bool) : (v.load o).read = o := rfl

/-- Pops a source bit and pushes it onto the destination before looping to `again`, or executes
`done` when the source is empty. -/
def moveStmt (src dst : Slot) (again : Label)
    (done : TM2.Stmt (fun _ : Slot => Bool) Label Local) :
    TM2.Stmt (fun _ : Slot => Bool) Label Local :=
  .pop src Local.load (.branch (fun v => v.read.isSome)
    (.push dst (fun v => v.read.getD false) (.load Local.clear (.goto (fun _ => again)))) done)

/-- For distinct stacks and the specified loop code, `xs.length + 1` steps empty the source and
prepend `xs.reverse` to the destination, then execute `done` with no read symbol. -/
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

/-- Pairs a bit with a true marker as `[b, true]` when `swapped` is true and `[true, b]`
otherwise. -/
def bitPair (swapped b : Bool) : Bits := if swapped then [b,true] else [true,b]

/-- Pops a source bit and pushes its `bitPair` onto the destination before looping to `again`,
or executes `done` when the source is empty. -/
def pairStmt (src dst : Slot) (again : Label) (swapped : Bool)
    (done : TM2.Stmt (fun _ : Slot => Bool) Label Local) :
    TM2.Stmt (fun _ : Slot => Bool) Label Local :=
  .pop src Local.load (.branch (fun v => v.read.isSome)
    (.push dst (fun v => if swapped then true else v.read.getD false)
      (.push dst (fun v => if swapped then v.read.getD false else true)
        (.load Local.clear (.goto (fun _ => again))))) done)

/-- For distinct stacks and the specified loop code, `xs.length + 1` steps empty the source and
prepend the concatenated `bitPair` encodings of `xs.reverse` to the destination, then
execute `done` with no read symbol. -/
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
