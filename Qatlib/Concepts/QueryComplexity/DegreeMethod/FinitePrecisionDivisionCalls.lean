/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader

/-!
# Multiplication calls in rational division

This module embeds either multiplication call into the division stack machine using `callCode`
and `returnCode`. The theorem `call_execution` transports both the exact execution result and
its stack clock, leaving the surrounding operand stacks fixed. The finite machine model has the
computational background described in [KitaevShenVyalyi2002].

## Main statements

* `callCode`: embeds multiplication labels into the first or second call.
* `call_execution`: identifies the returned product stack and preserves the multiplication
  clock.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.PairZip
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Turing
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Bits)
open Qatlib
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks

/-- Embeds a multiplication label into the second division call when `which` is true and into
the first call otherwise. -/
def callCode (which : Bool) (l : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.Label) : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Label :=
  if which then .second l else .first l

/-- Selects the return label for the chosen multiplication call: output initialization for the
second call and numerator saving for the first. -/
def returnCode (which : Bool) :
    Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Label :=
    if which then .startOutput else .saveNumerator

/-- Either embedded multiplication call returns the reversed product in work stack `2` after
`sourceSteps x y` steps, preserving the surrounding stacks and resetting the multiplication
state. Its stack clock equals that of the standalone multiplication run. -/
theorem call_execution (which : Bool) (x y A D B C raw : Bits) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local) :
    let start := (⟨some (callCode which .parse),v.putMul MulVar.init,
      Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store (Function.update (fun _ => []) (5 : Fin 6) (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.frame x++y)) A D B C raw⟩ :
      TM2.Cfg (fun _ : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Slot => Bool) Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Label Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local)
    stackRun Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.sourceSteps x y) start =
      some ⟨some (returnCode which),v.putMul MulVar.init,
        Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store (Function.update (fun _ => []) (2 : Fin 6) (mulAcc x y y.length).reverse) A D B C raw⟩ ∧
    stackRunClock Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.sourceSteps x y) start =
      stackRunClock Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.sourceSteps x y)
        (TM2.init (5 : Fin 6) (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.mulInput x y).reverse) := by
  have he (S : Fin 6 → Bits) (k : Fin 6) :
      Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store S A D B C raw (.inl k) = S k := rfl
  have hu (S : Fin 6 → Bits) (k : Fin 6) (bits : Bits) :
      Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store (Function.update S k bits) A D B C raw =
        Function.update (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store S A D B C raw) (.inl k) bits := by
    simpa only [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store,StackCall.leftFrame] using!
      StackCall.leftFrame_update ![A,D,B,C,raw] S k bits
  have hc (l : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.Label) : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program (callCode which l) =
      StackCall.stmt Sum.inl (callCode which) (returnCode which) Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.mul Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.putMul
        (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program l) := by
    cases which <;> rfl
  have h := StackCall.execution (stackCode:=Sum.inl) (labelCode:=callCode which)
    (returnTo:=returnCode which) (get:=Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.mul) (put:=Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.putMul)
    (E:=fun S => Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store S A D B C raw) (hE:=he) (hupdate:=hu)
    (hget:=fun _ _ => rfl) (hput:=fun _ _ _ => rfl)
    Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program hc v (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.sourceSteps x y) _ _ (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExecution.raw_execution x y)
  simpa only [StackCall.cfg,TM2.init,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.mulInput,List.reverse_reverse,
    Option.map_some,Option.getD_some,Option.map_none,Option.getD_none] using! h

end Qatlib.Concepts.QueryComplexity.DegreeMethod
