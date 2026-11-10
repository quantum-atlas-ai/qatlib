/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionPreparation
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatTag
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.ReadonlyCompare
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.TableCopy
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionParsing
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionPreparation

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionOutput

open Turing
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Bits)
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks

theorem startOutput_run (N E : Bits) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local) :
    stackRun Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program 1 ⟨some .startOutput,v,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionPreparation.work 2 E.reverse) N [] [] [] []⟩ =
      some ⟨some .numerator,v,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionPreparation.work 2 E.reverse) N [v.signA ^^ v.signB,true] [] [] []⟩ := by
  simp [stackRun,TM2.step,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program,TM2.stepAux]

theorem numerator_run (N E tailBits : Bits) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local) :
    stackRun Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program (N.length+1)
      ⟨some .numerator,v,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionPreparation.work 2 E.reverse) N tailBits [] [] []⟩ =
      some ⟨some .reverseDenominator,v.clear,
        Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionPreparation.work 2 E.reverse) [] ((Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.frame N).reverse++tailBits) [] [] []⟩ := by
  have h := pair_run (.inr 0) (.inr 1) .numerator true
    (.push (.inr 1) (fun _ => false) (.load Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.clear (.goto (fun _ => .reverseDenominator))))
    rfl (by decide) N tailBits (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionPreparation.work 2 E.reverse) [] [] [] [] []) v
  simpa [setTwo,TM2.stepAux,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.clear,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.load,frame_reverse] using! h

theorem reverseDenominator_run (E tailBits : Bits) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local) :
    stackRun Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program (E.length+1)
      ⟨some .reverseDenominator,v,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionPreparation.work 2 E.reverse) [] tailBits [] [] []⟩ =
      some ⟨some .denominator,v.clear,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionPreparation.work 0 E) [] tailBits [] [] []⟩ := by
  have h := move_run (.inl 2) (.inl 0) .reverseDenominator
    (.load Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.clear (.goto (fun _ => .denominator))) rfl (by decide)
    E.reverse [] (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store emptyWork [] tailBits [] [] []) v
  have hw : Function.update (Function.update emptyWork (2 : Fin 6) E.reverse) 0 [] =
      Function.update emptyWork 2 E.reverse := by
    funext k
    fin_cases k <;> simp [emptyWork]
  simpa [setTwo,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionPreparation.work,List.reverse_reverse,TM2.stepAux,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.clear,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.load,hw] using! h

theorem denominator_run (E tailBits : Bits) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local) :
    stackRun Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program (E.length+1)
      ⟨some .denominator,v,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionPreparation.work 0 E) [] tailBits [] [] []⟩ =
      some ⟨none,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.init,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store emptyWork [] (E.reverse++tailBits) [] [] []⟩ := by
  have h := move_run (.inl 0) (.inr 1) .denominator
    (.load (fun _ => Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.init) .halt) rfl (by decide)
    E tailBits (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store emptyWork [] [] [] [] []) v
  simpa [setTwo,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionPreparation.work,TM2.stepAux] using! h

def outputSteps (N E : Bits) : ℕ := 1+(N.length+1)+(E.length+1)+(E.length+1)

theorem output_run (sa sb : Bool) (A D B C N E : Bits) :
    stackRun Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program (outputSteps N E)
      ⟨some .startOutput,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionParsing.parsed sa sb A D B C,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionPreparation.work 2 E.reverse) N [] [] [] []⟩ =
      some ⟨none,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.init,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store emptyWork [] (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.output sa sb N E).reverse [] [] []⟩ := by
  rw [show outputSteps N E = 1+((N.length+1)+((E.length+1)+(E.length+1))) by
    dsimp [outputSteps]; omega]
  rw [run_add,startOutput_run,Option.bind_some,run_add,numerator_run,Option.bind_some,
    parsed_clear,run_add,reverseDenominator_run,Option.bind_some,parsed_clear,denominator_run]
  simp [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.output,List.reverse_cons,List.append_assoc,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionParsing.parsed,afterWord]

end Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionOutput
