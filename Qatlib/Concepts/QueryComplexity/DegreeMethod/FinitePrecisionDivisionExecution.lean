/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionOutput

/-!
# Successful execution of rational division

This module composes parsing, operand preparation, two multiplication calls, and output into an
exact successful run of the division stack program. The count `successSteps` accounts for each
phase; `raw_success` gives the final configuration when both denominators and the divisor
numerator have positive binary value. The underlying finite computation model is discussed in
[KitaevShenVyalyi2002].

## Main statements

* `success_run`: proves successful execution under the parsed validity check.
* `raw_success`: produces the encoded cross products with all other stacks empty.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Cleanup
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Emitter
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionOutput
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionParsing
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionPreparation
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Turing
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Bits)
open Qatlib
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks

/-- The total stack step count for reading valid division inputs, preparing and executing both
multiplication calls, and emitting the result. -/
def successSteps (A D B C : Bits) : ℕ :=
  readerSteps A D B C + 1 + (C.length+1) + (A.length+1) + sourceSteps A C +
    ((mulAcc A C C.length).length+1) + (B.length+1) + (D.length+1) + sourceSteps D B +
    outputSteps (mulAcc A C C.length) (mulAcc D B B.length)

/-- A true parsed validity flag sends the machine from the test label to `loadC` in one step
without changing its local state or stacks. -/
theorem test_valid_run (sa sb : Bool) (A D B C : Bits)
    (hvalid : (parsed sa sb A D B C).valid = true) :
    stackRun Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program 1
      ⟨some .test,parsed sa sb A D B C,store emptyWork A.reverse D.reverse B.reverse C.reverse []⟩ =
      some ⟨some .loadC,parsed sa sb A D B C,
        store emptyWork A.reverse D.reverse B.reverse C.reverse []⟩ := by
  simp [stackRun,TM2.step,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program,TM2.stepAux,hvalid]

/-- If the parsed validity flag is true, the division program halts after `successSteps` with
the reversed successful cross product encoding in the output stack, initialized local state,
and all other stacks empty. -/
theorem success_run (sa sb : Bool) (A D B C : Bits)
    (hvalid : (parsed sa sb A D B C).valid = true) :
    stackRun Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program (successSteps A D B C)
      (TM2.init (Sum.inr (4 : Fin 5) : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Slot) (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.input sa sb A D B C).reverse) =
      some ⟨none,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.init,
        store emptyWork [] (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.output sa sb (mulAcc A C C.length) (mulAcc D B B.length)).reverse [] [] []⟩ := by
  have hfirst := (call_execution false A C [] D.reverse B.reverse [] []
    (parsed sa sb A D B C)).1
  have hsecond := (call_execution true D B (mulAcc A C C.length) [] [] [] []
    (parsed sa sb A D B C)).1
  simp only [callCode,returnCode,Bool.false_eq_true,↓reduceIte,parsed_putMul] at hfirst
  simp only [callCode,returnCode,↓reduceIte,parsed_putMul] at hsecond
  have he : (fun _ : Fin 6 => ([] : Bits)) = emptyWork := rfl
  have hw (k : Fin 6) (xs : Bits) :
      Function.update emptyWork k xs = Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionPreparation.work k xs := rfl
  simp only [he,hw] at hfirst hsecond
  rw [show successSteps A D B C = readerSteps A D B C + (1 + ((C.length+1) +
      ((A.length+1) + (sourceSteps A C + (((mulAcc A C C.length).length+1) +
      ((B.length+1) + ((D.length+1) + (sourceSteps D B +
      outputSteps (mulAcc A C C.length) (mulAcc D B B.length))))))))) by
    dsimp [successSteps]; omega]
  rw [run_add,reader_raw,Option.bind_some]
  simp only [he]
  rw [run_add,test_valid_run sa sb A D B C hvalid,
    Option.bind_some,run_add,loadC_run,Option.bind_some,parsed_clear,
    run_add,frameA_run,Option.bind_some,parsed_clear,
    run_add,hfirst,Option.bind_some,run_add,saveNumerator_run,Option.bind_some,parsed_clear,
    run_add,loadB_run,Option.bind_some,parsed_clear,
    run_add,frameD_run,Option.bind_some,parsed_clear,run_add,hsecond,Option.bind_some]
  exact output_run sa sb A D B C _ _

/-- Positive binary values of `D`, `B`, and `C` ensure that division halts after `successSteps`
with the successful cross product encoding as its only nonempty stack. -/
theorem raw_success (sa sb : Bool) (A D B C : Bits)
    (hD : 0 < Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue D)
    (hB : 0 < Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue B)
    (hC : 0 < Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue C) :
    stackRun Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program (successSteps A D B C)
      (TM2.init (Sum.inr (4 : Fin 5) : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Slot) (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.input sa sb A D B C).reverse) =
      some ⟨none,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.init,
        Function.update (fun _ => []) (Sum.inr (1 : Fin 5) : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Slot)
          (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.output sa sb (mulAcc A C C.length) (mulAcc D B B.length)).reverse⟩ := by
  rw [success_run sa sb A D B C (parsed_nonzero sa sb A D B C hD hB hC)]
  congr 2
  funext k
  cases k with
  | inl k => simp [store,emptyWork]
  | inr k => fin_cases k <;> simp [store]

end Qatlib.Concepts.QueryComplexity.DegreeMethod
