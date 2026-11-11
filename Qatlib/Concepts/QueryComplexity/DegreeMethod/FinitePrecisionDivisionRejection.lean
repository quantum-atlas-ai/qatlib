/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionExecution

/-!
# Rejection in checked rational division

This module verifies the rejection branch of the division stack program. When the parsed
validity flag is false, `reject_run` proves that the operand stacks are drained and the machine
halts with the failure word `[false]`; `zero_divisor_rejected` specializes this to an empty
divisor numerator. The finite computation framework has background in [KitaevShenVyalyi2002].

## Main statements

* `drain_run`: specifies emptying one stack before a continuation.
* `reject_run`: gives the final rejection configuration and exact step count.
* `zero_divisor_rejected`: rejects the encoded zero divisor with empty numerator.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.FrameCopy
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.GuardedCounter
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.TableCopy
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.WordValidator
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionParsing
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionPreparation
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Turing
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Bits binaryValue)
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks

/-- Pops and discards a bit, returning to `again` when one is present and executing `done` when
the source stack is empty. -/
def drainStmt (src : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Slot) (again : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Label)
    (done : TM2.Stmt (fun _ : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Slot => Bool) Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Label Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local) :
    TM2.Stmt (fun _ : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Slot => Bool) Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Label Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local :=
  .pop src Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.load (.branch (fun v => v.read.isSome)
    (.load Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.clear (.goto (fun _ => again))) done)

/-- When `again` implements `drainStmt`, running for `xs.length + 1` steps empties the source
stack and executes `done` with no read symbol. -/
theorem drain_run (src : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Slot) (again : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Label)
    (done : TM2.Stmt (fun _ : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Slot => Bool) Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Label Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local)
    (hcode : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program again = drainStmt src again done)
    (xs : Bits) (S : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Slot → Bits) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local) :
    stackRun Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program (xs.length+1) ⟨some again,v,Function.update S src xs⟩ =
      some (TM2.stepAux done (v.load none) (Function.update S src [])) := by
  induction xs generalizing v with
  | nil => simp [stackRun,TM2.step,hcode,drainStmt,TM2.stepAux]
  | cons b bs ih =>
      have hs : TM2.step Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program ⟨some again,v,Function.update S src (b::bs)⟩ =
          some ⟨some again,v.clear,Function.update S src bs⟩ := by
        simp [TM2.step,hcode,drainStmt,TM2.stepAux,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.load,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.clear]
      rw [List.length_cons,stackRun,hs,Option.bind_some,ih]
      rfl

/-- The total step count for reading the input, failing the validity check, and draining the
four operand stacks. -/
def rejectSteps (A D B C : Bits) : ℕ :=
  readerSteps A D B C + 1 + (A.length+1) + (D.length+1) + (B.length+1) + (C.length+1)

/-- A false parsed validity flag makes the division program halt after `rejectSteps` with
initialized local state, the failure word `[false]` in the output stack, and all other
stacks empty. -/
theorem reject_run (sa sb : Bool) (A D B C : Bits)
    (hv : (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionParsing.parsed sa sb A D B C).valid = false) :
    stackRun Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program (rejectSteps A D B C)
      (TM2.init (Sum.inr (4 : Fin 5) : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Slot) (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.input sa sb A D B C).reverse) =
      some ⟨none,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.init,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store emptyWork [] [false] [] [] []⟩ := by
  let v :=
      Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionParsing.parsed sa sb A D B C
  have ht : stackRun Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program 1
      ⟨some .test,v,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store emptyWork A.reverse D.reverse B.reverse C.reverse []⟩ =
      some ⟨some (.invalid 0),v,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store emptyWork A.reverse D.reverse B.reverse C.reverse []⟩ := by
    simp [stackRun,TM2.step,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program,TM2.stepAux,hv,v]
  have hA := drain_run (.inr 0) (.invalid 0)
    (.load Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.clear (.goto (fun _ => .invalid 1))) rfl A.reverse
    (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store emptyWork [] D.reverse B.reverse C.reverse []) v
  have hD := drain_run (.inr 1) (.invalid 1)
    (.load Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.clear (.goto (fun _ => .invalid 2))) rfl D.reverse
    (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store emptyWork [] [] B.reverse C.reverse []) v
  have hB := drain_run (.inr 2) (.invalid 2)
    (.load Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.clear (.goto (fun _ => .invalid 3))) rfl B.reverse
    (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store emptyWork [] [] [] C.reverse []) v
  have hC := drain_run (.inr 3) (.invalid 3)
    (.push (.inr 1) (fun _ => false) (.load (fun _ => Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.init) .halt)) rfl C.reverse
    (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store emptyWork [] [] [] [] []) v
  simp only [List.length_reverse,store_update0,store_update1,store_update2,store_update3,
    TM2.stepAux,store1,clear_load] at hA hD hB hC
  have hclear : v.clear = v := rfl
  simp only [hclear] at hA hD hB
  rw [show rejectSteps A D B C = readerSteps A D B C +
      (1+((A.length+1)+((D.length+1)+((B.length+1)+(C.length+1))))) by
    dsimp [rejectSteps]; omega]
  rw [run_add,reader_raw,Option.bind_some]
  change (stackRun Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program _ ⟨some .test,v,
    Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store emptyWork A.reverse D.reverse B.reverse C.reverse []⟩) = _
  rw [run_add,ht,Option.bind_some,run_add,hA,
    Option.bind_some,run_add,hD,Option.bind_some,run_add,hB,Option.bind_some]
  simpa only [store_update1] using! hC

/-- An empty divisor numerator makes the division program halt after `rejectSteps` with the
failure word `[false]`, initialized local state, and all other stacks empty. -/
theorem zero_divisor_rejected (sa sb : Bool) (A D C : Bits) :
    stackRun Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program (rejectSteps A D [] C)
      (TM2.init (Sum.inr (4 : Fin 5) : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Slot) (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.input sa sb A D [] C).reverse) =
      some ⟨none,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.init,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store emptyWork [] [false] [] [] []⟩ := by
  apply reject_run
  simp [parsed_valid]

end Qatlib.Concepts.QueryComplexity.DegreeMethod
